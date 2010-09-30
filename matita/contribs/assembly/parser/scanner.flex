/* ******************************** */
/* PER UNA CORRETTA VISUALIZZAZIONE */
/*           tab size=4             */
/* ******************************** */

/* - stati del preprocessore */
%x	defbegin
%x	defend

/* - discard dei commenti / * ...  * / */
%x	combegin

%{

/* ************************************************************************* */

#include	<stdio.h>
#include	<stdlib.h>
#include	<string.h>

/* ************************************************************************* */

#define		MAX_DEPTH	1000	/* numero massimo di annidamenti */

#define		ERR_EXIT	0		/* uscita ok */
#define		OK_EXIT		1		/* uscita errore */

#define		SEP			'\n'	/* separatore dei campi in output */

#define		EXP_OPT		"-e"	/* opzione di solo preprocessing */

/* stringhe di errore */
#define		ERR_UNK		"ScanError:UnknownToken"
#define		ERR_OPT		"ScanError:UnknownOption"
#define		ERR_NL		"ScanError:UnexptedNewline"
#define		ERR_STR		"ScanError:EmptyString"
#define		ERR_CHR		"ScanError:EmptyChar"
#define		ERR_ALR		"ScanError:RepeatedDefine"
#define		ERR_MANYCHR	"ScanError:TooManyChars"
#define		ERR_INC		"ScanError:TooManyExpansionsOrNestings"
#define		ERR_MIS		"ScanError:MissingIncludeFile"
#define		ERR_MEM		"ScanError:OutOfMemory"
#define		ERR_ARG		"ScanError:IncorrectArgumentNumber"
#define		ERR_OPEN	"ScanError:FileNotFound"
#define		ERR_UNA		"ScanError:UnallowedExpansion"
#define		ERR_UNE		"ScanError:Unexpected(#endif)"
#define		ERR_UNS		"ScanError:Unexpected(#switch)"
#define		ERR_END		"ScanError:Missing(#endif)"
#define		ERR_LOP		"ScanError:ExpansionLoopDetected"
#define		ERR_RES		"ScanError:ReservedToken"

/* ************************************************************************* */

/* elemento lista dei token */
typedef struct listElem
	{
	char				*scanTxt;
	struct listElem		*next;
	} listELEM;

/* elemento lista delle espansioni */
typedef struct defElem
	{
	char				*defId;
	char				*defTxt;
	struct defElem		*next;
	} defELEM;

/* ************************************************************************* */

YY_BUFFER_STATE		inStream[MAX_DEPTH];			/* buffer: input stream buffer */
int					inNesting=0;					/* contatore: livello di annidamento */
char				inName[MAX_DEPTH][257];			/* buffer: nomi dei sorgenti */
int					inLine[MAX_DEPTH];				/* buffer: linea corrente */
int					inRow[MAX_DEPTH];				/* buffer: colonna corrente */

listELEM			*rootElem=NULL,*curElem=NULL;	/* lista dei token */
defELEM				*rootDef=NULL,*curDef=NULL;		/* lista delle espansioni */

int					stringFound;					/* flag: stringa non vuota */
int					charFound;						/* flag: carattere non vuoto */
int					expand=0;						/* flag: espansione in corso */
int					startExpansion;					/* variabile: espansione iniziale (per evitare loop) */
int					eatTrueEndif=0;					/* contatore: #endif validi (a seguito di true) */
int					eatFalseEndif=0;				/* contatore: #endif validi (a seguito di false) */
int					expOnly=0;						/* flag: preprocessare senza generare token */

char				tempBuf[2000];					/* spazio temporaneo per formattare l'output/error */

/* espansioni riservate */
char	*reserved[]={
			"array",
			"of",
			"struct",
			"if",
			"elsif",
			"else",
			"while",
			"const",
			"b2w",
			"b2dw",
			"w2b",
			"w2dw",
			"dw2b",
			"dw2w",
			"byte",
			"word",
			"dword",
			NULL };

/* ************************************************************************* */

void	addOkBuf(char *token,char *ytext);
void	errExit(char *ytext);
void	addDefId(char *ytext);
int		checkDefId(char *ytext);
void	checkRsvd(char *ytext);
void	delDefId(char *ytext);
void	addDefTxt(char *ytext);
void	usage(char *name);

/* ************************************************************************* */

%}

KEYWORD		("array"|"of"|"struct"|"if"|"elsif"|"else"|"while"|"const"|"b2w"|"b2dw"|"w2b"|"w2dw"|"dw2b"|"dw2w")
TYPE		("byte"|"word"|"dword")
BRACKET		("{"|"}"|"["|"]"|"("|")")
MONOOP		("!"|"~")
DUALOP		("&"|"|"|"^"|"+"|"-"|"*"|"/"|"!="|"=="|"<"|">"|"<="|">="|"<<"|">>"|"=")
SEPARATOR	(";"|"."|",")

IDWORD		("0x"[a-fA-F0-9][a-fA-F0-9][a-fA-F0-9][a-fA-F0-9][a-fA-F0-9][a-fA-F0-9][a-fA-F0-9][a-fA-F0-9])
IWORD		("0x"[a-fA-F0-9][a-fA-F0-9][a-fA-F0-9][a-fA-F0-9])
IBYTE		("0x"[a-fA-F0-9][a-fA-F0-9])
INUM		([0-9]+)
ID			([_a-zA-Z][_a-zA-Z0-9]*)

BLANK		([ \t])
NL			(\n|\r\n)

/* ************************************************************************* */

%%

<INITIAL>"#define"		{
						/* ************** */
						/* DEFINIZIONE ID */
						/* ************** */

						if(expand)
							{ sprintf(tempBuf,"%s",ERR_UNA); errExit(tempBuf); exit(ERR_EXIT); }

						inRow[inNesting]+=yyleng;
						BEGIN(defbegin);
						}
<defbegin>{BLANK}+		{ inRow[inNesting]+=yyleng; }
<defbegin>{ID}			{ checkRsvd(yytext); addDefId(yytext); inRow[inNesting]+=yyleng; BEGIN(defend); }
<defbegin>{NL}			{ sprintf(tempBuf,"%s",ERR_NL); errExit(tempBuf); exit(ERR_EXIT); }
<defbegin>.				{ sprintf(tempBuf,"%s(%s)",ERR_UNK,yytext); errExit(tempBuf); exit(ERR_EXIT); }	
<defend>[^\r\n]+		{ addDefTxt(yytext); inRow[inNesting]+=yyleng; }
<defend>{NL}			{ inLine[inNesting]++; inRow[inNesting]=1; BEGIN(INITIAL); }



<INITIAL>"/*"			{
						/* *************** */
						/* INIZIO COMMENTO */
						/* *************** */
						
						if(!expand)
							{ inRow[inNesting]+=yyleng; }
							
						BEGIN(combegin);
						}
<combegin>{NL}			{
						if(expand)
							{ sprintf(tempBuf,"%s",ERR_NL); errExit(tempBuf); exit(ERR_EXIT); }

						inLine[inNesting]++;
						inRow[inNesting]=1;
						}
<combegin>[^\r\n]		{
						if(!expand)
							{ inRow[inNesting]+=yyleng; }
						}
<combegin>"*/"			{
						if(!expand)
							{ inRow[inNesting]+=yyleng; }
						
						BEGIN(INITIAL);
						}



<INITIAL>{KEYWORD}		{
						/* ******************** */
						/* TOKEN DEL LINGUAGGIO */
						/* ******************** */

						addOkBuf("KEW",yytext);
						
						if(!expand)
							{ inRow[inNesting]+=yyleng; }
						}
<INITIAL>{TYPE}			{
						addOkBuf("TYP",yytext);
						
						if(!expand)
							{ inRow[inNesting]+=yyleng; }
						}
<INITIAL>{BRACKET}		{
						addOkBuf("BRK",yytext);
						
						if(!expand)
							{ inRow[inNesting]+=yyleng; }
						}
<INITIAL>{MONOOP}		{
						addOkBuf("MOP",yytext);
						
						if(!expand)
							{ inRow[inNesting]+=yyleng; }
						}
<INITIAL>{DUALOP}		{
						addOkBuf("DOP",yytext);
						
						if(!expand)
							{ inRow[inNesting]+=yyleng; }
						}
<INITIAL>{SEPARATOR}	{
						addOkBuf("SEP",yytext);
						
						if(!expand)
							{ inRow[inNesting]+=yyleng; }
						}
<INITIAL>{IDWORD}		{
						addOkBuf("W32",yytext);
						
						if(!expand)
							{ inRow[inNesting]+=yyleng; }
						}
<INITIAL>{IWORD}		{
						addOkBuf("W16",yytext);
						
						if(!expand)
							{ inRow[inNesting]+=yyleng; }
						}
<INITIAL>{IBYTE}		{
						addOkBuf("BY8",yytext);
						
						if(!expand)
							{ inRow[inNesting]+=yyleng; }
						}
<INITIAL>{INUM}			{
						addOkBuf("INU",yytext);
						
						if(!expand)
							{ inRow[inNesting]+=yyleng; }
						}



<INITIAL>{ID}			{
						/* ********************* */
						/* TOKEN ID O ESPANSIONE */
						/* ********************* */

						defELEM	*tmp;
						int		found=0;
						int		index;

						for(index=0,tmp=rootDef;tmp;tmp=tmp->next,index++)
							{
							if(!strcmp(tmp->defId,yytext))
								{
								found=1;

								/* Prima espansione */
								if(!expand)
									{
									startExpansion=index;
									break;
									}
								/* Espansione dentro un'espansione */
								else if(startExpansion!=index)
									{ break; }
								/* Loop detected */
								else
									{ sprintf(tempBuf,"%s",ERR_LOP); errExit(tempBuf); exit(ERR_EXIT); }
								}
							}

						/* espandi */
						if(found)
							{
							expand++;

							if(inNesting>=MAX_DEPTH)
								{ sprintf(tempBuf,"%s",ERR_INC); errExit(tempBuf); exit(ERR_EXIT); }

							inStream[inNesting++]=YY_CURRENT_BUFFER;
							inLine[inNesting]=inLine[inNesting-1];
							inRow[inNesting]=inRow[inNesting-1];
							if(expand<2)
								{ inRow[inNesting-1]+=yyleng; }
							strcpy(inName[inNesting],inName[inNesting-1]);
			
							/* cambio di input stream -> espansione */
							if(tmp->defTxt)
								{ yy_scan_string(tmp->defTxt); }
							else
								{ yy_scan_string(""); }
							}
						/* genera token */
						else
							{
							addOkBuf("IID",yytext);

							if(!expand)
								{ inRow[inNesting]+=yyleng; }
							}
						}



<INITIAL>{BLANK}+		{
						/* **************** */
						/* NEW LINE E BLANK */
						/* **************** */

						if(expOnly)
							{ printf("%s",yytext); }
						if(!expand)
							{ inRow[inNesting]+=yyleng; }
						}
<INITIAL>{NL}			{
						if(expOnly)
							{ printf("%s",yytext); }
						if(expand)
							{ sprintf(tempBuf,"%s",ERR_NL); errExit(tempBuf); exit(ERR_EXIT); }

						inLine[inNesting]++;
						inRow[inNesting]=1;
						}



<INITIAL,defend><<EOF>>	{
						/* **************************************** */
						/* EOF = FINE DI UN'ESPANSIONE O INCLUSIONE */
						/* **************************************** */

						if((--inNesting)<0)
							{
							if(eatTrueEndif||eatFalseEndif)
								{ ++inNesting; sprintf(tempBuf,"%s",ERR_END); errExit(tempBuf); exit(ERR_EXIT); }

							yyterminate();
							}
						else
							{
							yy_delete_buffer(YY_CURRENT_BUFFER);
							yy_switch_to_buffer(inStream[inNesting]);
							}

						if(expand)
							{ expand--; }
						}



<INITIAL>.				{
						/* ************************** */
						/* CARATTERE NON RICONOSCIUTO */
						/* ************************** */
					
						sprintf(tempBuf,"%s(%s)",ERR_UNK,yytext);
						errExit(tempBuf);
						exit(ERR_EXIT);
						}				

%%

/* ************************************************************************* */

/* formattazione dell'errore ed uscita */
void errExit(char *ytext)
{
	printf("%s:%d,%d\tERR\t%s\t%c",inName[inNesting],inLine[inNesting],inRow[inNesting],ytext,SEP);
}

/* ************************************************************************* */

/* controllo se ID e' gia' stato definito come espansione */
int checkDefId(char *ytext)
{
	defELEM	*tmp;

	for(tmp=rootDef;tmp;tmp=tmp->next)
		{
		if(!strcmp(tmp->defId,ytext))
			{ return(1); }
		}

	return(0);
}

/* ************************************************************************* */

/* controllo se ID corrisponde ad un elemento di reserved[] */
void checkRsvd(char *ytext)
{
	int	index;

	for(index=0;reserved[index];index++)
		{
		if(!strcmp(reserved[index],ytext))
			{ sprintf(tempBuf,"%s(%s)",ERR_RES,yytext); errExit(tempBuf); exit(ERR_EXIT);}
		}

	return;
}

/* ************************************************************************* */

/* allocazione di ID come nuova espansione */
void addDefId(char *ytext)
{
	if(!rootDef)
		{ 
		if(!(curDef=rootDef=(defELEM *) malloc(sizeof(defELEM))))
			{ sprintf(tempBuf,"%s",ERR_MEM); errExit(tempBuf); exit(ERR_EXIT); }
		}
	else
		{
		defELEM	*tmp;

		for(tmp=rootDef;tmp;tmp=tmp->next)
			{
			if(!strcmp(tmp->defId,ytext))
				{ sprintf(tempBuf,"%s",ERR_ALR); errExit(tempBuf); exit(ERR_EXIT); }
			}

		if(!(curDef->next=(defELEM *) malloc(sizeof(defELEM))))
			{ sprintf(tempBuf,"%s",ERR_MEM); errExit(tempBuf); exit(ERR_EXIT); }

		curDef=curDef->next;
		}

	curDef->next=NULL;
	curDef->defTxt=NULL;

	if(!(curDef->defId=(char *) malloc(strlen(ytext)+1)))
		{ sprintf(tempBuf,"%s",ERR_MEM); errExit(tempBuf); exit(ERR_EXIT); }

	strcpy(curDef->defId,ytext);

	return;
}

/* ************************************************************************* */

/* rimozione di ID come espansione */
void delDefId(char *ytext)
{
	defELEM	*tmp,*prevTmp;

	for(prevTmp=NULL,tmp=rootDef;tmp;prevTmp=tmp,tmp=tmp->next)
		{
		if(!strcmp(tmp->defId,ytext))
			{
			if(prevTmp)
				{
				prevTmp->next=tmp->next;

				free(tmp->defId);
				if(tmp->defTxt)
					{ free(tmp->defTxt); }
				free(tmp);
				}
			else
				{
				rootDef=tmp->next;

				free(tmp->defId);
				if(tmp->defTxt)
					{ free(tmp->defTxt); }
				free(tmp);
				}

			break;
			}
		}

	return;
}

/* ************************************************************************* */

/* definizione del testo dell'espansione di ID */
void addDefTxt(char *ytext)
{
	if(!(curDef->defTxt=(char *) malloc(strlen(ytext)+1)))
		{ sprintf(tempBuf,"%s",ERR_MEM); errExit(tempBuf); exit(ERR_EXIT); }

	strcpy(curDef->defTxt,ytext);

	return;
}

/* ************************************************************************* */

/* formattazione e aggiunta di yytext alla lista dei token */
void addOkBuf(char *token,char *ytext)
{
	if(expOnly)
		{ printf("%s",ytext); }
	else
		{
		sprintf(tempBuf,"%s:%d,%d\t%s\t%s\t%c",inName[inNesting],inLine[inNesting],inRow[inNesting],token,ytext,SEP);

		if(!rootElem)
			{
			if(!(curElem=rootElem=(listELEM *) malloc(sizeof(listELEM))))
				{ sprintf(tempBuf,"%s",ERR_MEM); errExit(tempBuf); exit(ERR_EXIT); }
			}
		else
			{
			if(!(curElem->next=(listELEM *) malloc(sizeof(listELEM))))
				{ sprintf(tempBuf,"%s",ERR_MEM); errExit(tempBuf); exit(ERR_EXIT); }

			curElem=curElem->next;
			}

		curElem->next=NULL;

		if(!(curElem->scanTxt=(char *) malloc(strlen(tempBuf)+1)))
		 { sprintf(tempBuf,"%s",ERR_MEM); errExit(tempBuf); exit(ERR_EXIT); }

		strcpy(curElem->scanTxt,tempBuf);
		}

	return;
}

/* ************************************************************************* */

void usage(char *name)
{
	printf("\nC Scanner - Cosimo Oliboni\n\n");
	printf("\"%s -e source\" preprocessing di un sorgente\n",name);
	printf("\"%s source\" scanning di un sorgente\n",name);
	printf("\"%s\" scanning da stdin\n\n",name);

	return;
}

/* ************************************************************************* */

int main(int argc, char **argv)
{
	inLine[inNesting]=0;
	inRow[inNesting]=0;

	if(argc>1)
		{
		/* "scanner -e sorgente" */
		if(argc==3)
			{
			if(strcmp(argv[1],EXP_OPT))
				{ sprintf(tempBuf,"%s",ERR_OPT); errExit(tempBuf); usage(argv[0]); exit(ERR_EXIT); }

			expOnly=1;

			strcpy(inName[inNesting],argv[2]);
			}
		/* "scanner sorgente" */
		else if(argc==2)
			{ strcpy(inName[inNesting],argv[1]); }
		else
			{ sprintf(tempBuf,"%s",ERR_ARG); errExit(tempBuf); usage(argv[0]); exit(ERR_EXIT); }

		if(!(yyin=fopen(inName[inNesting],"r")))
			{ sprintf(tempBuf,"%s(%s)",ERR_OPEN,inName[inNesting]); errExit(tempBuf); usage(argv[0]); exit(ERR_EXIT); }
		}
	/* "scanner <stdin>" */
	else
		{ strcpy(inName[inNesting],"stdin"); }

	inLine[inNesting]=1;
	inRow[inNesting]=1;

	/* scanning */
	yylex();

	/* se non ci sono stati errori && se non si effettua solo preprocessing */
	/* output della lista di token creata */
	/* preceduta da OK && seguita da EOF */

	if(!expOnly)
		{
		inNesting++;

		addOkBuf("EOF","EOF");

		printf("%s:0,0\tOK\tOK\t%c",inName[0],SEP);

		for(curElem=rootElem;curElem;curElem=curElem->next)
			{ printf("%s",curElem->scanTxt); }
		}

	return(OK_EXIT);
}

yywrap()
{
	return(1);
}
