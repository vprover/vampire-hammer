.PHONY: all clean

all: parser.tab.c lex.yy.c

parser.tab.c parser.tab.h: parser.y
	bison -d $<

lex.yy.c: lexer.l parser.tab.h
	flex $<

clean:
	rm -rf lex.yy.* parser.tab.*
