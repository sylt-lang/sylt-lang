#!/usr/bin/env python3
import sys
from json import loads

def format(name, comment, signature):
    def parse_sig(sig):
        def parse_arg(arg):
            def parse_type(ty):
                i = ty.find("(")
                ty, name = ty[:i].strip().lower(), ty[i+1:].strip(" )")
                if name == "":
                    return "()"
                return f"<span class='name'>{name}</span>:<span class='ty'>{ty}</span>"

            i = arg.find("(")
            pre, arg_list = arg[:i], arg[i+1:].split(",")
            args = ", ".join(map(parse_type, arg_list))
            if args.count(",") >= 1:
                args = f"({args})"
            return f"<span class='arg'>{args}</span>"

        def parse_ret(ret):
            return ret.replace("Type :: ", "").lower()

        args, ret = sig.split("->")
        args = ", ".join(map(parse_arg, args[1:-2].split(")),")))
        ret = parse_ret(ret)
        return f"<li><span class='fn'>fn</span> <span class='args'>{args}</span> <span class='arrow'>-></span> <span class='ret'>{ret}</span></li>"

    sigs = "\n".join(parse_sig(sig) for sig in signature)

    return f"""<div class='fun'>
                 <h2 id='{name}'>{name}</h2>
                 <div class='comment'>{comment}</div>
                 <ul class='sigs'>{sigs}</ul>
             </div>"""

def tok(name, **_):
    return f"<li><a href='#{name}'>{name}</a></li>"

preamble = f"""
<html>
<head>
<title>Lingon Sylt documentation</title>
<style>
{open("docs.css").read()}
</style>
</head>
<body>
<h1>THE Lingon Sylt documentation</h1>
"""

postamble = """
</body>
</html>
"""

def main(args):
    if len(args) != 2:
        print("Usage: {} docs.json", args[0])
        sys.exit(1)

    with open("docs.html", "w") as docs:
        docs.write(preamble)

        docs.write("<ul class='tok'>")
        for element in loads(open(args[1]).read()):
            docs.write(tok(**element))
        docs.write("</ul>")

        for element in loads(open(args[1]).read()):
            docs.write(format(**element))

        docs.write(postamble)

if __name__ == "__main__":
    main(sys.argv)
