flex -oscanner.c scanner.flex

d:
cd \
cd Programmi\GnuWin32\bin\
bison.exe H:\Esami\Tesi\Sorgenti\parser\parser.y
copy parser.tab.c H:\Esami\Tesi\Sorgenti\parser\parser.c
del parser.tab.c

h:
