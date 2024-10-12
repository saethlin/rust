//~ ERROR overflow evaluating the requirement `{closure@rt::lang_start<()>::{closure#0}}: Freeze`
//~| HELP consider increasing the recursion limit
//@ build-fail

#![recursion_limit = "0"]

fn main() {}
