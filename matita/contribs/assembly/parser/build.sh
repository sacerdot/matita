
flex scanner.flex
gcc -o scanner lex.yy.c
bison parser.y
gcc -o parser parser.tab.c
rm -f lex.yy.c parser.tab.c
