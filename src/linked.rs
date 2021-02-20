#[sylt_macro::extern_link]
pub fn f(x: sylt::Value, _typecheck: bool) -> Result<sylt::Value, sylt::error::ErrorKind> {
    Ok(x)
}

#[sylt_macro::extern_link(g)]
pub fn f2(x: sylt::Value, _typecheck: bool) -> Result<sylt::Value, sylt::error::ErrorKind> {
    Ok(x)
}

mod m1 {
    mod m2 {
        #[sylt_macro::extern_link(h)]
        pub fn f2(x: sylt::Value, _typecheck: bool) -> Result<sylt::Value, sylt::error::ErrorKind> {
            Ok(x)
        }
    }
}
