# lists the available just recipes
default:
  @just --list

# regenerate tree-sitter artifacts
[working-directory: 'tree-sitter-jabber']
build-parser:
  tree-sitter generate

# build compiler with the given profile
[working-directory: 'compiler']
build profile='dev': build-parser
  cargo build --profile {{profile}} --quiet

# run the given program
[working-directory: 'compiler']
run program: build-parser
  cargo run --quiet -- -l "../libs" run -s "../support" -i "../{{program}}"
