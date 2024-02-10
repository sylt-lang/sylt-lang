#![allow(dead_code)]

use std::cmp::Ordering;
use std::collections::btree_map::Entry;
use std::collections::BTreeMap;
use std::collections::BTreeSet;

use crate::error::*;
use crate::name_resolution::*;

// TODO[et]: I should write unit tests for the typechecker, that is actually quite easy now...

// [[ Maintainers note 2023-02-21 ]]
// This module is very complex, this is true, but fear not for some key insights can really help
// this module make sense.
//
// This typesystem is my  implementation of a Damas–Hindley–Milner typesystem, but what does that
// mean?
// Obligatory wikipedia reference: https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system
//
// This type system can deduce types itself, and reason about your entire program as a whole. This
// makes it so you are not required to write types anywhere, the computer checks the types for you,
// like magic! Unfortunately it has limitations with some more fancy kinds of types, which aren't
// present in sylt as of now.
//
// People give the rules slightly different names, but there are 4 things we can do in the
// typesystem.
//  1. We can unify types, this is handled by the `unify` function. This means the type-system
//     knows that two types are exactly the same. For example `a = b` would cause a unification of
//     the types of `a` and `b` since we assign them to each other we know they have to have the
//     same type. These rules get a bit intricate for some types, but they are pretty straight
//     forward.
//
//  2. Specialization/substitution, handled by `raise_generics_to_unknowns` takes a type that is
//     not specialized, e.g. `forall a. a -> a` and substitutes the generic with a new named type.
//     This makes it possible to unify a generic, like `a` with an actual type `Int`, since a
//     generic stands for "any possible type". Note especially that we keep equality of types
//     though, so after this substitution we get a type like `#1 -> #1`.
//     Substitutes makes it possible to unify later.
//
//  3. Some types are a bit more special than simple types such as `Int` or `Bool`. Records are
//     handled in a different way, namely with requirements on types this concept is similar to
//     type-classes (for the OOP people think interfaces). So we can attach the requirement "has
//     a field `.field`" to a type. We then verify these rules after a unification to make sure
//     they are kept.
//
//  4. We know the type of a constant. So if you write `1`, we know it's an `Int`. This gets a bit
//     more tricky when it comes to `Real` and `Int` since you might write `1` but expect the
//     compiler to automatically cast it to `Real` in the comparison or whatever, this is not done
//     at all in Sylt-lang.
//
// There are some limitations of this implementation though. It would be nice to remove the
// assumption of certain types from the type_checker file, it doesn't need to know about `Int` or
// `Bool`, just that things return something called `Int` or `Bool`.
//

#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq)]
pub enum CType<'t> {
  NodeType(NameId),
  // TODO - add Error type so we can report multiple errors and stuff
  Unknown,
  Foreign(&'t Name<'t>),
  // Is this a good idea to code here?
  // Generics do not need to take up node types
  Generic(usize),
  Record(BTreeMap<FieldId, NameId>, bool),
  // TODO: Can the element type be a NameId? Remove Apply and use Function everywhere.
  Apply(Box<CType<'t>>, Vec<CType<'t>>),
  Function(Box<CType<'t>>, Box<CType<'t>>),
  // We couldn't figure out the type - this value marks our typechecker giving up
  Error,
}

impl<'t> CType<'t> {
  fn is_same(&self, other: &Self) -> bool {
    match (self, other) {
      (CType::Unknown, CType::Unknown) => true,
      (CType::Record(a, aa), CType::Record(b, bb)) => a == b && aa == bb,
      (CType::Foreign(a), CType::Foreign(b)) => a == b,
      (CType::NodeType(a), CType::NodeType(b)) => a == b,
      (CType::Generic(a), CType::Generic(b)) => a == b,
      _ => false,
    }
  }
}

impl<'t> CType<'t> {
  // The public function
  pub fn render_to_string(
    &self,
    types: Vec<Node<'t>>,
    names: &'t Vec<Name<'t>>,
    fields: &'t BTreeMap<FieldId, &'t str>,
  ) -> String {
    // TODO: We need to clone types for now, but we should be able to not clone it later by
    // having a mutable borrow - preferably CType shouldn't care about Checker.
    let mut checker = Checker {
      types,
      names,
      fields,
      aliases: BTreeMap::new(),
      instances: BTreeMap::new(),
      errors: Vec::new(),
    };
    self.render(&mut checker)
  }

  fn render(&self, checker: &mut Checker<'t>) -> String {
    self.render_inner(checker)
  }

  fn render_inner(&self, checker: &mut Checker<'t>) -> String {
    match self {
      CType::NodeType(name) => {
        let ty = resolve_ty(checker, *name);
        format!("<#{} {}>", name.0, ty.render(checker))
      }
      CType::Unknown => "_".to_string(),
      CType::Foreign(name) => format!("'{} {}'", name.name.0, name.name.1),
      // This isn't good enough
      CType::Record(fields, open) => {
        let mut out = "".to_string();
        for (i, (fid, ty)) in fields.iter().enumerate() {
          if i != 0 {
            out = format!("{}, ", out);
          }
          out = format!(
            "{} {}: {}",
            out,
            checker.fields.get(fid).unwrap(),
            resolve_ty(checker, *ty).render_inner(checker)
          );
        }
        format!("{{ {} {} }}", out, if *open { " | _ " } else { "" })
      }
      CType::Apply(a, bs) => {
        let a = a.render(checker);
        let bs = bs
          .iter()
          .map(|b| b.render(checker))
          .collect::<Vec<_>>()
          .join(" ");
        format!("{} {}", a, bs)
      }
      CType::Function(a, b) => {
        let a = a.render(checker);
        let b = b.render(checker);
        format!("{} -> {}", a, b)
      }
      CType::Generic(i) => {
        format!("t{}", *i)
      }
      CType::Error => {
        format!("?")
      }
    }
  }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Requirement {
  Class(NameId),
  Field(FieldId, NameId),
}

impl PartialOrd for Requirement {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl Ord for Requirement {
  fn cmp(&self, other: &Self) -> Ordering {
    fn to_tuple(s: &Requirement) -> (usize, usize) {
      match s {
        Requirement::Field(FieldId(n), _) => (1, *n),
        Requirement::Class(NameId(id)) => (2, *id),
      }
    }

    to_tuple(self).cmp(&to_tuple(other))
  }
}

impl Requirement {
  fn to_name<'t>(&self, checker: &mut Checker<'t>) -> String {
    match self {
      Requirement::Field(field, ty) => {
        format!(
          "({}: {})",
          checker.field(*field),
          CType::NodeType(*ty).render(checker)
        )
      }
      Requirement::Class(class) => {
        format!("(class {})", checker.name(*class),)
      }
    }
  }
}

#[derive(Clone, Debug)]
pub enum Node<'t> {
  Child(NameId),
  // Remove this indirection!
  Ty(CType<'t>),
}

struct Checker<'t> {
  types: Vec<Node<'t>>,
  names: &'t [Name<'t>],
  fields: &'t BTreeMap<FieldId, &'t str>,
  aliases: BTreeMap<NameId, (&'t Vec<NameId>, CType<'t>)>,

  // TODO - It's never been a good idea to add more complexity here, so I doubt this is the best
  // way to do this
  instances: BTreeMap<NameId, BTreeSet<CType<'t>>>,

  errors: Vec<Error>,
}

impl<'t> Checker<'t> {
  fn field(&self, field: FieldId) -> &'t str {
    &self.fields[&field]
  }

  fn add_err(&mut self, err: Error) {
    self.errors.push(err);
  }

  fn name(&self, NameId(slot): NameId) -> String {
    format!(
      "'{} {}'",
      &self.names[slot].name.0, &self.names[slot].name.1
    )
  }

  // This function is really expensive memory wise. Removing a call to this function is big profit!
  fn raise_to_node(&mut self, ty: CType<'t>) -> NameId {
    match ty {
      CType::NodeType(id) => id,
      ty => {
        // We get a bunch of dangling nodes - they can consume a lot of memory but I don't think
        // they're a problem. The naive and simple optimizations are already done. It's more
        // problematic some of the types are `unknown` after the typechecker has run.
        let name = NameId(self.types.len());
        self.types.push(Node::Ty(ty));
        name
      }
    }
  }

  fn catch(&self, CatchCounter(cc): CatchCounter) -> bool {
    self.errors.len() == cc
  }

  fn tryy(&self) -> CatchCounter {
    CatchCounter(self.errors.len())
  }
}

struct CatchCounter(usize);

pub fn check<'a, 't>(
  names: &'t Vec<Name<'t>>,
  defs: &'a Vec<Def>,
  fields: &'t BTreeMap<FieldId, &'t str>,
) -> (Vec<Node<'t>>, Vec<Error>)
where
  'a: 't,
{
  // These are the only nodes which should ever be created. Otherwise memory usage will explode.
  let mut checker = Checker {
    types: names
      .iter()
      .enumerate()
      .map(|(i, Name { is_generic, .. })| {
        if *is_generic {
          Node::Ty(CType::Generic(i))
        } else {
          Node::Ty(CType::Unknown)
        }
      })
      .collect(),
    names,
    fields,
    aliases: BTreeMap::new(),
    instances: BTreeMap::new(),
    errors: Vec::new(),
  };

  for def in defs {
    match def {
      // Args that are unused cannot exist, what are they going to limit
      Def::Type { name, args, body, span } => {
        let NameId(slot) = name;
        unify(
          &mut checker,
          CType::NodeType(*name),
          CType::Foreign(&names[*slot]),
          *span,
        );

        let def_ty = check_type(&mut checker, body);
        checker.aliases.insert(*name, (args, def_ty));
      }

      Def::Class(class) => {
        match checker.instances.entry(*class) {
          Entry::Vacant(e) => {
            e.insert(BTreeSet::new());
          }
          Entry::Occupied(_) => unreachable!("We dissallow multiple names, how did we get here?"),
        }
        unify(
          &mut checker,
          CType::NodeType(*class),
          CType::Generic(0),
          Span(0, 0, 0),
        );
      }

      Def::ForeignType { name, args, span } => {
        let NameId(slot) = name;
        let args = args.iter().map(|a| CType::NodeType(*a)).collect();
        let def_ty = CType::Apply(Box::new(CType::Foreign(&names[*slot])), args);
        unify(&mut checker, CType::NodeType(*name), def_ty, *span);
      }

      Def::Enum { name, args, span } => {
        let NameId(slot) = name;
        let args = args.iter().map(|a| CType::NodeType(*a)).collect();
        let def_ty = CType::Apply(Box::new(CType::Foreign(&names[*slot])), args);
        unify(&mut checker, CType::NodeType(*name), def_ty, *span);
      }

      _ => {}
    }
  }
  for def in defs {
    match def {
      Def::Def { ty, name, args: _, body: _, span } => {
        // Args and body are checked later
        let ty = check_type(&mut checker, ty);
        unify(&mut checker, CType::NodeType(*name), ty, *span);
      }
      _ => {}
    }
  }

  // Why does this help? Do I allow unifying without knowing all the information? How bad is
  // this in respect to performance and memory?
  for _ in 0..2 {
    for def in defs {
      check_def(&mut checker, def);
    }
  }
  for (i, t) in checker.types.clone().iter().enumerate() {
    match (t, checker.names.get(i).clone()) {
      (Node::Ty(t), Some(n)) => check_everything_makes_sense(&mut checker, t.clone(), t, n.def_at),
      _ => {}
    }
  }

  (checker.types, checker.errors)
}

// NOTE[et]: There's still a major problem with typeclasses. Calling discards
// requirements, so typeclasses aren't a thing that are checked in any meaningful way (it would
// also be really nice if there were dependencies with typeclasses but I should be able to solve
// all this at the same time)
//
// Given this function:
//   def i: let Num a. a -> a : a = a + a
//
// Consider this program that does not compile:
//   def main ::= i "A"
//
// And then this program that *does* compile despite not being correct:
//   def main ::= i ' "A"
//
// What I believe is happening is the changes to operators meant that this is actually more calls
// and is actually equivalent to:
//   def xcall :: f a = f a
//   def main ::= call i "A"
// here xcall discards the requirements and the function typechecks since generics are converted to
// unknowns which unify with everything.
// I propose to store requirements in a seperate list (this is what the literature also
// discusses) that is checked when copied from generics. That way we can also check ONLY the
// requirements.
fn check_everything_makes_sense<'t>(
  checker: &mut Checker<'t>,
  t: CType<'t>,
  tt: &CType<'t>,
  span: Span,
) {
  match t {
    // I'll get to the node type eventually...
    CType::NodeType(_) => {}
    CType::Unknown => {
      error_expected(
        checker,
        "Failed to resolve this type - it is still unknown",
        tt.clone(),
        span,
      );
    }
    CType::Error => {
      error_expected(
        checker,
        "Failed to resolve this type - it's an error type",
        tt.clone(),
        span,
      );
    }
    CType::Foreign(_) => {}
    CType::Generic(_) => {}
    CType::Record(fields, _) => {
      for (_fid, ty) in fields.iter() {
        check_everything_makes_sense(checker, CType::NodeType(*ty), tt, span);
      }
    }
    CType::Apply(f, xs) => {
      check_everything_makes_sense(checker, *f, tt, span);
      for x in xs.iter() {
        check_everything_makes_sense(checker, x.clone(), tt, span);
      }
    }
    CType::Function(a, b) => {
      check_everything_makes_sense(checker, *a, tt, span);
      check_everything_makes_sense(checker, *b, tt, span);
    }
  }
}

fn check_def(checker: &mut Checker, def: &Def) {
  match def {
    Def::Def { ty: _, name, args, body, span } => {
      // Type is checked earlier
      let mut def_ty = CType::Unknown;
      for arg in args.iter().rev() {
        let arg = check_pattern(checker, arg);
        def_ty = CType::Function(Box::new(arg), Box::new(def_ty));
      }
      let ty = unify(checker, CType::NodeType(*name), def_ty, *span);
      let mut body_ty = check_expr(checker, body);
      for _ in args.iter() {
        body_ty = CType::Function(Box::new(CType::Unknown), Box::new(body_ty));
      }
      unify(checker, body_ty, ty, *span);
    }
    Def::ForiegnDef { ty, name, span, foreign_block: _ } => {
      let def_ty = check_type(checker, ty);
      unify(checker, CType::NodeType(*name), def_ty, *span);
    }
    Def::Type { .. } => {
      // TODO! More needs to be done here, mainly with higher order types and stuff
    }
    Def::Enum { .. } => {
      // TODO! More needs to be done here, mainly with higher order types and stuff
    }
    Def::Class(..) => {
      // TODO! More needs to be done here, mainly with higher order types and stuff
    }
    Def::Instance { class, ty } => {
      let ty = check_type(checker, ty);
      assert!(checker.instances.contains_key(class), "Should always contain the key since class definitions are done before hand, but maybe this should be an actual error?");
      checker.instances.get_mut(class).unwrap().insert(ty);
    }

    Def::ForeignType { .. } => { /* Do nothing */ }
  }
}

fn record_merge<'t>(
  new: BTreeMap<FieldId, NameId>,
  old: BTreeMap<FieldId, NameId>,
) -> BTreeMap<FieldId, NameId> {
  let mut out = old;
  for (fid, ty) in new.into_iter() {
    out.insert(fid, ty);
  }
  out
}

fn check_eq<'t>(checker: &mut Checker<'t>, a: &CType<'t>, b: &CType<'t>) -> bool {
  // If they're equal, they're equal
  a == b
    || match (a, b) {
      // Ignore unknowns
      (CType::Unknown, _) => true,
      (_, CType::Unknown) => true,
      // If it's a pointer, dig a bit deeper
      (CType::NodeType(a_id), CType::NodeType(b_id)) => {
        resolve(checker, &a_id) == resolve(checker, &b_id)
      }
      (CType::NodeType(a_id), b) => {
        let inner_a = resolve_ty(checker, *a_id);
        check_eq(checker, &inner_a, b)
      }
      (a, CType::NodeType(b_id)) => {
        let inner_b = resolve_ty(checker, *b_id);
        check_eq(checker, a, &inner_b)
      }
      // Equality for foreign types is well defined
      (CType::Foreign(a), CType::Foreign(b)) => a.def_at == b.def_at,
      // NOTE[et]: Should be same case as function, which is much simpler
      (CType::Apply(a0, a1), CType::Apply(b0, b1)) => {
        a1.len() == b1.len()
          && check_eq(checker, a0, b0)
          && a1
            .iter()
            .zip(b1.iter())
            .all(|(a, b)| check_eq(checker, a, b))
      }
      // NOTE[et]: Equality for function types, because why not?
      (CType::Function(a0, a1), CType::Function(b0, b1)) => {
        check_eq(checker, a0, b0) && check_eq(checker, a1, b1)
      }
      // Not a match
      (_, _) => false,
    }
}

fn unify<'t>(checker: &mut Checker<'t>, a: CType<'t>, b: CType<'t>, span: Span) -> CType<'t> {
  // println!("{} + {}", a.render(checker), b.render(checker));
  match (a, b) {
    (a, b) if a == b => a,
    (CType::Error, other) | (other, CType::Error) => other,
    (CType::Unknown, b) => b,
    (a, CType::Unknown) => a,
    (CType::Record(ar, ao), CType::Record(br, bo)) => {
      let cc = checker.tryy();
      let mut cr = BTreeMap::new();
      for (id, a_ty) in ar.iter() {
        match br.get(id) {
          Some(b_ty) => {
            unify(
              checker,
              CType::NodeType(*a_ty),
              CType::NodeType(*b_ty),
              span,
            );
            cr.insert(*id, *a_ty);
          }
          None if bo => {
            cr.insert(*id, *a_ty);
          }
          None => {
            error_unify(
              checker,
              "There are extra labels in one record (R)",
              CType::Record(ar.clone(), ao),
              CType::Record(br.clone(), bo),
              span,
            );
          }
        }
      }
      for (id, b_ty) in br.iter() {
        match ar.get(id) {
          Some(a_ty) => {
            unify(
              checker,
              CType::NodeType(*a_ty),
              CType::NodeType(*b_ty),
              span,
            );
            cr.insert(*id, *a_ty);
          }
          None if ao => {
            cr.insert(*id, *b_ty);
          }
          None => {
            error_unify(
              checker,
              "There are extra labels in one record (L)",
              CType::Record(ar.clone(), ao),
              CType::Record(br.clone(), bo),
              span,
            );
          }
        }
      }
      if checker.catch(cc) {
        CType::Error
      } else {
        CType::Record(cr, ao && bo)
      }
    }
    // Prevents infinite recursion if we've linked a lot of things, which really isn't a problem.
    (CType::NodeType(a_id), CType::NodeType(b_id))
      if resolve(checker, &a_id) == resolve(checker, &b_id) =>
    {
      CType::NodeType(a_id)
    }
    (CType::NodeType(a_id), b) => {
      let inner_a = resolve_ty(checker, a_id);
      let c = unify(checker, inner_a, b, span);
      inject(checker, a_id, c);
      CType::NodeType(a_id)
    }
    (a, CType::NodeType(b_id)) => {
      let inner_b = resolve_ty(checker, b_id);
      let c = unify(checker, a, inner_b, span);
      inject(checker, b_id, c);
      CType::NodeType(b_id)
    }
    (CType::Foreign(a), CType::Foreign(b)) if a.def_at == b.def_at => CType::Foreign(a),
    (CType::Foreign(a), CType::Foreign(b)) if a.def_at != b.def_at => {
      error_unify(
        checker,
        "Failed to merge these types",
        CType::Foreign(a),
        CType::Foreign(b),
        span,
      );
      CType::Error
    }
    (CType::Apply(a0, a1), CType::Apply(b0, b1)) if a1.len() == b1.len() => {
      let c0 = unify(checker, *a0, *b0, span);
      let c1 = a1
        .into_iter()
        .zip(b1.into_iter())
        .map(|(ax, bx)| unify(checker, ax, bx, span))
        .collect::<Vec<_>>();
      CType::Apply(Box::new(c0), c1)
    }
    (a @ CType::Apply(_, _), b @ CType::Apply(_, _)) => {
      error_unify(
        checker,
        "The number of type arguments doesn't match here",
        a,
        b,
        span,
      );
      CType::Error
    }
    (CType::Function(a0, a1), CType::Function(b0, b1)) => {
      let c0 = unify(checker, *a0, *b0, span);
      let c1 = unify(checker, *a1, *b1, span);
      CType::Function(Box::new(c0), Box::new(c1))
    }
    (a @ CType::Generic(_), b @ CType::Generic(_)) => {
      error_unify(
        checker,
        "Escaped generics, how did you get here? Please send me the code",
        a,
        b,
        span,
      );
      CType::Error
    }
    (a, b) => {
      error_unify(checker, "Failed to merge types", a, b, span);
      CType::Error
    }
  }
}

fn check_expr<'t>(checker: &mut Checker<'t>, body: &Expr) -> CType<'t> {
  match body {
    Expr::Var(name, _) => raise_generics_to_unknowns(checker, CType::NodeType(*name)),
    Expr::EnumConst { ty_name, value, const_name: _, span } => {
      let ty = CType::NodeType(*ty_name);
      match value {
        Some((expr, exp_ty)) => {
          let exp_ty = check_type(checker, exp_ty);
          let expr_ty = check_expr(checker, expr);
          let f_ty = CType::Function(Box::new(exp_ty), Box::new(ty));
          let f_ty = raise_generics_to_unknowns(checker, f_ty);
          let call_ty = CType::Function(Box::new(expr_ty), Box::new(CType::Unknown));
          if let CType::Function(_, out_ty) = unify(checker, f_ty, call_ty, *span) {
            *out_ty
          } else {
            unreachable!("We have to return a function when unifying with a function!");
          }
        }
        None => raise_generics_to_unknowns(checker, ty),
      }
    }
    Expr::Let { bind_value, binding, next_value } => {
      let out = check_expr(checker, next_value);

      let bind_value_ty = check_expr(checker, bind_value);
      let binding_ty = check_pattern(checker, binding);
      unify(checker, bind_value_ty, binding_ty, binding.span());
      out
    }
    Expr::Record { to_extend, fields, span } => {
      let mut ff = BTreeMap::new();
      for ((span, field), value) in fields.iter() {
        let ty = check_expr(checker, value);
        let ty = checker.raise_to_node(ty);
        if let Some(_) = ff.get(field) {
          panic!(
            "Multiple of the same field {:?}, {:?}",
            checker.field(*field),
            span
          );
        }
        ff.insert(*field, ty);
      }
      // TODO: Return error node here?
      CType::Record(
        match to_extend {
          None => ff,
          Some(to_extend) => {
            let extend_ty = check_expr(checker, to_extend);
            match dig(checker, extend_ty) {
              CType::Record(extend, false) => record_merge(ff, extend),
              CType::NodeType(_) => unreachable!(),
              a @ (CType::Unknown
              | CType::Error
              | CType::Foreign(_)
              | CType::Generic(_)
              | CType::Apply(_, _)
              | CType::Record(_, _)
              | CType::Function(_, _)) => {
                error_expected(checker, "Expected a Record here", a, *span);
                ff
              }
            }
          }
        },
        false,
      )
    }
    Expr::If { condition, bool, t, f, span } => {
      let c_ty = check_expr(checker, condition);
      unify(checker, c_ty, CType::NodeType(*bool), *span);
      let t = check_expr(checker, t);
      let f = check_expr(checker, f);
      unify(checker, t, f, *span)
    }
    Expr::Match { value, branches, span: _ } => {
      let mut outer_match_ty = check_expr(checker, value);

      // NOTE[]: There's different ways of doing this, it might be more nice to depth-first
      // instead of breath first.
      for WithBranch { pattern, condition: _, value: _, bool: _, span } in branches.iter() {
        let pattern_ty = check_pattern(checker, pattern);
        outer_match_ty = unify(checker, pattern_ty, outer_match_ty, *span);
      }

      for WithBranch { pattern: _, condition, value: _, bool, span } in branches.iter() {
        if let Some(condition) = condition {
          let condition_ty = check_expr(checker, condition);
          unify(checker, condition_ty, CType::NodeType(*bool), *span);
        }
      }

      let mut ret_ty = CType::Unknown;
      for WithBranch { pattern: _, condition: _, value, bool: _, span } in branches.iter() {
        let value_ty = check_expr(checker, value);
        ret_ty = unify(checker, value_ty, ret_ty, *span);
      }

      ret_ty
    }

    Expr::Lambda { args, body, span: _ } => {
      let body = check_expr(checker, body);
      let mut def_ty = body;
      for arg in args.iter().rev() {
        let arg = check_pattern(checker, arg);
        def_ty = CType::Function(Box::new(arg), Box::new(def_ty));
      }
      def_ty
    }
    Expr::Call(f, a, at) => {
      let f_ty = check_expr(checker, f);
      let a_ty = check_expr(checker, a);
      // Can this be removed?
      match unify(
        checker,
        f_ty,
        CType::Function(Box::new(a_ty), Box::new(CType::Unknown)),
        *at,
      ) {
        CType::NodeType(name) => {
          if let CType::Function(_, ret) = resolve_ty(checker, name) {
            *ret
          } else {
            CType::Error
          }
        }
        CType::Function(_, ret) => *ret,
        _ => CType::Error,
      }
    }
    Expr::EBool(_, _, ty) | Expr::EInt(_, _, ty) | Expr::EReal(_, _, ty) | Expr::EStr(_, _, ty) => {
      CType::NodeType(*ty)
    }
  }
}

fn raise_generics_to_unknowns<'t>(checker: &mut Checker<'t>, ty: CType<'t>) -> CType<'t> {
  fn generic_helper<'t>(
    checker: &mut Checker<'t>,
    ty: CType<'t>,
    generics_to_node_types: &mut BTreeMap<usize, NameId>,
  ) -> CType<'t> {
    match ty {
      CType::Unknown | CType::Error | CType::Foreign(_) => ty,

      CType::Record(fields, o) => CType::Record(
        fields
          .into_iter()
          .map(|(f, t)| {
            (f, {
              // NOTE[et]: Is this wrong? Shouldn't this be `generic_helper`?
              let ty = raise_generics_to_unknowns(checker, CType::NodeType(t));
              checker.raise_to_node(ty)
            })
          })
          .collect(),
        o,
      ),

      CType::Generic(i) => match generics_to_node_types.entry(i) {
        Entry::Vacant(v) => {
          let new_node = checker.raise_to_node(CType::Unknown);
          v.insert(new_node);
          CType::NodeType(new_node)
        }
        Entry::Occupied(o) => CType::NodeType(*o.get()),
      },

      CType::Apply(a, bs) => {
        let a = Box::new(generic_helper(checker, *a, generics_to_node_types));
        let bs = bs
          .into_iter()
          .map(|b| generic_helper(checker, b, generics_to_node_types))
          .collect();
        CType::Apply(a, bs)
      }
      CType::Function(a, b) => {
        let a = Box::new(generic_helper(checker, *a, generics_to_node_types));
        let b = Box::new(generic_helper(checker, *b, generics_to_node_types));
        CType::Function(a, b)
      }
      CType::NodeType(node) => {
        let ty = resolve_ty(checker, node);
        generic_helper(checker, ty, generics_to_node_types)
      }
    }
  }

  generic_helper(checker, ty, &mut BTreeMap::new())
}

fn check_pattern<'t>(checker: &mut Checker<'t>, binding: &Pattern) -> CType<'t> {
  match binding {
    Pattern::Empty(_) => CType::Unknown,
    Pattern::Var(var, inner, span) => {
      let var_ty = CType::NodeType(*var);
      match inner {
        Some(inner) => {
          let inner_ty = check_pattern(checker, inner);
          unify(checker, var_ty, inner_ty, *span)
        }
        None => var_ty,
      }
    }
    Pattern::EnumConst { ty_name, const_name: _, inner, span } => {
      let ty = CType::NodeType(*ty_name);
      match inner {
        Some((pat, exp_ty)) => {
          let exp_ty = check_type(checker, exp_ty);
          let pat_ty = check_pattern(checker, pat);
          let f_ty = CType::Function(Box::new(exp_ty), Box::new(ty));
          let f_ty = raise_generics_to_unknowns(checker, f_ty);
          let call_ty = CType::Function(Box::new(pat_ty), Box::new(CType::Unknown));
          if let CType::Function(_, out_ty) = unify(checker, f_ty, call_ty, *span) {
            *out_ty
          } else {
            unreachable!("We have to return a function when unifying with a function!");
          }
        }
        None => raise_generics_to_unknowns(checker, ty),
      }
    }
    Pattern::Record(fields, _) => {
      let mut ff = BTreeMap::new();
      for (field, field_span, pat) in fields.iter() {
        let value_ty = check_pattern(checker, pat);
        let value_node = checker.raise_to_node(value_ty);
        if ff.contains_key(field) {
          panic!(
            "Multiple of the same field {:?}, {:?}",
            checker.field(*field),
            field_span
          );
        }
        ff.insert(*field, value_node);
      }
      CType::Record(ff, true)
    }
    Pattern::PBool(_, _, ty)
    | Pattern::PInt(_, _, ty)
    | Pattern::PReal(_, _, ty)
    | Pattern::PStr(_, _, ty) => CType::NodeType(*ty),
  }
}

fn resolve<'t>(checker: &mut Checker<'t>, NameId(slot): &NameId) -> NameId {
  match checker.types[*slot] {
    Node::Child(parent) => {
      let at = resolve(checker, &parent);
      checker.types[*slot] = Node::Child(at);
      at
    }
    Node::Ty(_) => NameId(*slot),
  }
}

fn dig<'t>(checker: &mut Checker<'t>, a: CType<'t>) -> CType<'t> {
  match a {
    CType::NodeType(t) => {
      let tt = resolve_ty(checker, t);
      dig(checker, tt)
    }
    CType::Unknown
    | CType::Error
    | CType::Foreign(_)
    | CType::Generic(_)
    | CType::Record(_, _)
    | CType::Apply(_, _)
    | CType::Function(_, _) => a,
  }
}

// Think twice before using this function, it's usually better to keep thinks linked.
fn resolve_ty<'t>(checker: &mut Checker<'t>, a: NameId) -> CType<'t> {
  let NameId(slot) = resolve(checker, &a);
  if let Node::Ty(ty) = checker.types[slot].clone() {
    ty
  } else {
    panic!("Invariant doesn't hold! Not an inner most type!")
  }
}

fn inject<'t>(checker: &mut Checker<'t>, a_id: NameId, c: CType<'t>) {
  let NameId(slot) = resolve(checker, &a_id);
  match &c {
    CType::NodeType(c) if c == &a_id => panic!("Typechecker bug!"),
    CType::NodeType(c) if c != &a_id => checker.types[slot] = Node::Child(*c),
    c => checker.types[slot] = Node::Ty(c.clone()),
  }
}

fn check_type<'t>(checker: &mut Checker<'t>, ty: &Type) -> CType<'t> {
  match ty {
    Type::TApply(a, bs, span) => {
      let bs_ty = bs
        .iter()
        .map(|b| check_type(checker, b))
        .collect::<Vec<CType<'t>>>();
      let bs_ty = CType::Apply(Box::new(CType::Unknown), bs_ty);
      match check_type(checker, a) {
        CType::NodeType(n) if checker.aliases.contains_key(&n) => {
          let (args, body) = checker.aliases.get(&n).unwrap();
          let args_ty = args.iter().map(|a| CType::NodeType(*a)).collect();
          if let CType::Function(input, output) = raise_generics_to_unknowns(
            checker,
            CType::Function(
              Box::new(CType::Apply(Box::new(CType::Unknown), args_ty)),
              Box::new(body.clone()),
            ),
          ) {
            unify(checker, *input, bs_ty, *span);
            *output
          } else {
            unreachable!();
          }
        }
        a_ty => {
          let a_ty = raise_generics_to_unknowns(checker, a_ty);
          unify(checker, a_ty, bs_ty, *span)
        }
      }
    }
    Type::TNode(slot, _) => CType::NodeType(*slot),
    Type::TFunction(a, b, _) => {
      let a_ty = check_type(checker, a);
      let b_ty = check_type(checker, b);
      CType::Function(Box::new(a_ty), Box::new(b_ty))
    }
    Type::TRecord { fields, span: _ } => {
      let mut ff = BTreeMap::new();
      for (span, field, inner_ty) in fields.iter() {
        let value_ty = check_type(checker, inner_ty);
        let value_node = checker.raise_to_node(value_ty);
        if ff.contains_key(field) {
          panic!(
            "Multiple of the same field {:?}, {:?}",
            checker.field(*field),
            span
          );
        }
        ff.insert(*field, value_node);
      }
      CType::Record(ff, false)
    }
    Type::TConstraint { inner, .. } => check_type(checker, inner),
  }
}

fn error_expected<'t>(checker: &mut Checker<'t>, msg: &'static str, a: CType<'t>, span: Span) {
  let err = Error::CheckExpected { msg, span, a: a.render(checker) };
  checker.add_err(err);
}

fn error_unify<'t>(
  checker: &mut Checker<'t>,
  msg: &'static str,
  a: CType<'t>,
  b: CType<'t>,
  span: Span,
) {
  let err = Error::CheckUnify {
    msg,
    span,
    a: a.render(checker),
    b: b.render(checker),
  };
  checker.add_err(err);
}
