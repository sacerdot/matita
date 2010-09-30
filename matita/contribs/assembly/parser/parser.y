
/* ******************************** */
/* PER UNA CORRETTA VISUALIZZAZIONE */
/*           tab size=4             */
/* ******************************** */

%{

#include	<stdio.h>
#include	<stdlib.h>
#include	<string.h>
#include	<sys/types.h>

/* ************************************************************************* */

#define		YYDEBUG		1					/* debug interno di bison */

#define		inline							/* compatibilita' con l'opzione %glr-parser */
#define		YYLTYPE_IS_DECLARED	1			/* compatibilita' con VISUAL C */

#define		SEP			'\n'				/* formattazione in input */

#define		YYSTYPE		valueLeaf *			/* struttura puntata dai nodi/foglie */

#define		ERR_EXIT	-1

/* manipolazione della posizione nel sorgente (bison) */
#define		YYLLOC_DEFAULT(Current,Rhs,N) \
	do \
		if(N) \
			{ \
			(Current).first_line=YYRHSLOC(Rhs,1).first_line; \
			(Current).first_column=YYRHSLOC(Rhs,1).first_column; \
			(Current).last_line=YYRHSLOC(Rhs,N).last_line; \
			(Current).last_column=YYRHSLOC(Rhs,N).last_column; \
			(Current).source=YYRHSLOC(Rhs,1).source; \
			} \
		else \
			{ \
			(Current).first_line=(Current).last_line=YYRHSLOC(Rhs,0).last_line; \
			(Current).first_column=(Current).last_column=YYRHSLOC(Rhs,0).last_column; \
			(Current).source=YYRHSLOC(Rhs,0).source; \
			} \
	while(0)

#ifndef		__STDC__
#define		__STDC__

#define		myMalloc(x)			malloc((x<512) ? 512 : x)
typedef		unsigned __int32	_DWORD_;	/* definizione univoca DWORD */
typedef		unsigned __int16	_WORD_;		/* definizione univoca WORD */
typedef		unsigned __int8		_BYTE_;		/* definizione univoca BYTE */

#else

#define		myMalloc(x)			malloc((x<512) ? 512 : x)
typedef		__uint32_t			_DWORD_;	/* definizione univoca DWORD */
typedef		__uint16_t			_WORD_;		/* definizione univoca WORD */
typedef		__uint8_t			_BYTE_;		/* definizione univoca BYTE */

#endif

/* ************************************************************************* */

/* struttura per la posizione manipolata direttamente da YYLOC_DEFAULT (bison) */
typedef struct YYLTYPE
	{
	int		first_line;
	int		first_column;
	int		last_line;
	int		last_column;
	char	*source;
	} YYLTYPE;

/* enumerazione delle etichette dei nodi/foglie */
typedef enum {
	E_VALUE_ARRAY,
	E_VALUE_STRUCT,
	E_VALUE_DWORD,
	E_VALUE_WORD,
	E_VALUE_BYTE,
	E_VALUE_INUM,
	E_VALUE_STRING,

	E_DECL_CONST,
	E_DECL_VAR,

	E_STM_ASG,
	E_STM_WHILE,
	E_STM_IF,
	E_STM_IFEXPRBODY,

	E_EXPR_NEG,
	E_EXPR_NOT,
	E_EXPR_COM,
	E_EXPR_MUL,
	E_EXPR_DIV,
	E_EXPR_ADD,
	E_EXPR_SUB,
	E_EXPR_SHL,
	E_EXPR_SHR,
	E_EXPR_LT,
	E_EXPR_LTE,
	E_EXPR_GT,
	E_EXPR_GTE,
	E_EXPR_NEQ,
	E_EXPR_EQ,
	E_EXPR_AND,
	E_EXPR_OR,
	E_EXPR_XOR,
	E_EXPR_B2W,
	E_EXPR_B2DW,
	E_EXPR_W2B,
	E_EXPR_W2DW,
	E_EXPR_DW2B,
	E_EXPR_DW2W,
	E_EXPR_VAR,

	E_VAR_ROOT,
	E_VAR_STRUCT,
	E_VAR_ARRAY,

	E_TYPE_ARRAY,
	E_TYPE_STRUCT,
	E_TYPE_DWORD,
	E_TYPE_WORD,
	E_TYPE_BYTE,

	} vEnum;

/* struttura polimorfa dei nodi/foglie */
typedef struct _valueLeaf_
	{
	/* etichetta */
	vEnum				id;

	_DWORD_				dwordValue;
	_WORD_				wordValue;
	_BYTE_				byteValue;
	unsigned long int	inumValue;
	char				*stringValue;

	struct _valueLeaf_	*param1;
	struct _valueLeaf_	*param2;
	struct _valueLeaf_	*param3;
	struct _valueLeaf_	*param4;

	/* per tutti */
	struct _valueLeaf_	*next;
	struct _valueLeaf_	*last;

	/* posizione nel sorgente */
	int					fileLine;
	int					fileRow;
	char				*source;
	} valueLeaf;

/* ************************************************************************* */

valueLeaf	root;				/* radice dell'AST */
valueLeaf	*typeRoot=NULL;		/* radice degli user type */

int			numErr=0;

/* ************************************************************************* */

int			yylex(YYSTYPE *lvalp,YYLTYPE *llocp,void *p);
void		yyerror(const YYLTYPE *locp,void *p,char const *msg);
valueLeaf	*treeAlloc(\
				vEnum id,\
				_DWORD_ dwordValue,\
				_WORD_ wordValue,\
				_BYTE_ byteValue,\
				unsigned long int inumValue,\
				char *stringValue,\
				valueLeaf *param1,\
				valueLeaf *param2,\
				valueLeaf *param3,\
				const YYLTYPE *locp);

valueLeaf	*treeDwordAlloc(_DWORD_ dwordValue,const YYLTYPE *locp);
valueLeaf	*treeWordAlloc(_WORD_ wordValue,const YYLTYPE *locp);
valueLeaf	*treeByteAlloc(_BYTE_ byteValue,const YYLTYPE *locp);
valueLeaf	*treeInumAlloc(unsigned long int inumValue,const YYLTYPE *locp);
valueLeaf	*treeStringAlloc(char *stringValue,const YYLTYPE *locp);
valueLeaf	*treeId0Alloc(vEnum id,const YYLTYPE *locp);
valueLeaf	*treeId1Alloc(vEnum id,valueLeaf *param1,const YYLTYPE *locp);
valueLeaf	*treeId2Alloc(vEnum id,valueLeaf *param1,valueLeaf *param2,const YYLTYPE *locp);
valueLeaf	*treeId3Alloc(vEnum id,valueLeaf *param1,valueLeaf *param2,valueLeaf *param3,const YYLTYPE *locp);

int			eqUserType(valueLeaf *type1,valueLeaf *type2);
int			getUserType(valueLeaf *type,valueLeaf **res);
void		createUserType(valueLeaf *type);

void prettyPrint(valueLeaf *cur,int indent);

/* ************************************************************************* */

%}

%locations
%pure-parser
%lex-param		{void *p}
%parse-param	{void *p}
%error-verbose

/* ************************************************************************* */

/* keyword */
%token		Keyword_STRUCT		Keyword_ARRAY		Keyword_OF			
%token		Keyword_IF			Keyword_ELSIF		Keyword_ELSE		Keyword_WHILE		Keyword_CONST
%token		Keyword_B2W			Keyword_B2DW		Keyword_W2B			Keyword_W2DW		Keyword_DW2B		Keyword_DW2W

/* tipi nativi */
%token		Type_BYTE			Type_WORD			Type_DWORD

/* parentesi */
%token		OpenBracket_BODY	CloseBracket_BODY
%token		OpenBracket_SQUARE	CloseBracket_SQUARE
%token		OpenBracket_ROUND	CloseBracket_ROUND

/* operatori unari */
%token		UnaryOperator_NOT	UnaryOperator_COM

/* operatori duali */
%token		DualOperator_AND	DualOperator_OR		DualOperator_XOR
%token		DualOperator_ADD	DualOperator_SUB	DualOperator_MUL	DualOperator_DIV
%token		DualOperator_NEQ	DualOperator_EQ		DualOperator_LT		DualOperator_GT		DualOperator_LTE	DualOperator_GTE
%token		DualOperator_ASG	DualOperator_SHR	DualOperator_SHL

/* separatori */
%token		Separator_COLUMN	Separator_SELECT	Separator_COMMA

/* valori */
%token		Value_DWORD			Value_WORD			Value_BYTE			Value_INUM			Value_STRING

/* ************************************************************************* */

%start		_start_

/* priorita' minima */

%right		Separator_COMMA

%nonassoc	DualOperator_ASG

%nonassoc	Keyword_B2W			Keyword_B2DW		Keyword_W2B		Keyword_W2DW		Keyword_DW2B		Keyword_DW2W

%left		DualOperator_OR
%left		DualOperator_XOR
%left		DualOperator_AND

%nonassoc	DualOperator_NEQ
%nonassoc	DualOperator_EQ
%nonassoc	DualOperator_GTE
%nonassoc	DualOperator_GT
%nonassoc	DualOperator_LTE
%nonassoc	DualOperator_LT

%left		DualOperator_SHR
%left		DualOperator_SHL
%left		DualOperator_SUB
%left		DualOperator_ADD
%left		DualOperator_DIV
%left		DualOperator_MUL

%nonassoc	UnaryOperator_SUB
%nonassoc	UnaryOperator_COM
%nonassoc	UnaryOperator_NOT

%right		Separator_SELECT
%right		Separator_COLUMN

%nonassoc	OpenBracket_SQUARE	CloseBracket_SQUARE
%nonassoc	OpenBracket_ROUND	CloseBracket_ROUND	
%nonassoc	OpenBracket_BODY	CloseBracket_BODY

/* priorita' massima */	

/* ************************************************************************* */

%%

/* ** FUNZIONE PRINCIPALE ** */
_start_			:	OpenBracket_BODY _decl_lst_ CloseBracket_BODY
						{ memcpy(&root,$2,sizeof(valueLeaf)); };

/* ** GESTIONE DICHIARAZIONI ** */
_decl_lst_		:	Keyword_CONST _type_ Value_STRING DualOperator_ASG _init_choice_ Separator_COLUMN _decl_lst_
						{
						$$=treeId3Alloc(E_DECL_CONST,$2,$3,$5,&@1);
						$$->next=$7;
						}|
					_type_ Value_STRING _init_ Separator_COLUMN _decl_lst_
						{
						$$=treeId3Alloc(E_DECL_VAR,$1,$2,$3,&@1);
						$$->next=$5;						
						}|
					_stm_lst_
						{ $$=$1; };

_type_			:	Keyword_ARRAY OpenBracket_SQUARE Value_INUM CloseBracket_SQUARE Keyword_OF _type_
						{
						if(!($3->inumValue))
							{ yyerror(&@1,p,"unallowed empty array"); }
						else
							{
							$$=treeId2Alloc(E_TYPE_ARRAY,$3,$6,&@1);
							$3->inumValue--;
							}
						}|
					Keyword_STRUCT OpenBracket_BODY _type_ Separator_COLUMN _type_lst_ CloseBracket_BODY
						{
						$$=treeId1Alloc(E_TYPE_STRUCT,$3,&@1);
						$3->next=$5;

						createUserType($$);
						}|
					Type_DWORD
						{ $$=treeId0Alloc(E_TYPE_DWORD,&@1); }|
					Type_WORD
						{ $$=treeId0Alloc(E_TYPE_WORD,&@1); }|
					Type_BYTE
						{ $$=treeId0Alloc(E_TYPE_BYTE,&@1); };

_type_lst_		:	_type_ Separator_COLUMN _type_lst_
						{
						$1->next=$3;
						$$=$1;
						}|
					/* epsilon */
						{ $$=NULL; };

_init_			:	DualOperator_ASG _init_choice_
						{ $$=$2; }|
					/* epsilon */
						{ $$=NULL; };

_init_choice_	:	_init_val_
						{ $$=$1; }|
					_var_
						{ $$=$1; };

_init_val_		:	OpenBracket_SQUARE _init_val_ _init_val_lst_ CloseBracket_SQUARE
						{
						$$=treeId1Alloc(E_VALUE_ARRAY,$2,&@1);
						$2->next=$3;
						}|
					OpenBracket_BODY _init_val_ _init_val_lst_ CloseBracket_BODY
						{
						$$=treeId1Alloc(E_VALUE_STRUCT,$2,&@1);
						$2->next=$3;
						}|
					Value_DWORD
						{ $$=$1; }|
					Value_WORD
						{ $$=$1; }|
					Value_BYTE
						{ $$=$1; };

_init_val_lst_	:	Separator_COMMA _init_val_ _init_val_lst_
						{
						$2->next=$3;
						$$=$2;
						}|
					/* epsilon */
						{ $$=NULL; };

/* ** GESTIONE STATEMENT ** */
_stm_lst_		:	_var_ DualOperator_ASG _expr_ Separator_COLUMN _stm_lst_
						{
						$$=treeId2Alloc(E_STM_ASG,$1,$3,&@1);
						$$->next=$5;
						}|
					Keyword_WHILE OpenBracket_ROUND _expr_ CloseBracket_ROUND OpenBracket_BODY _decl_lst_ CloseBracket_BODY _stm_lst_
						{
						$$=treeId2Alloc(E_STM_WHILE,$3,$6,&@1);
						$$->next=$8;
						}|
					Keyword_IF OpenBracket_ROUND _expr_ CloseBracket_ROUND OpenBracket_BODY _decl_lst_ CloseBracket_BODY _elsif_lst_ _else_ _stm_lst_
						{
						$$=treeId2Alloc(E_STM_IF,treeId2Alloc(E_STM_IFEXPRBODY,$3,$6,&@1),$9,&@1);
						$$->param1->next=$8;
						$$->next=$10;
						}|
					/* epsilon */
						{ $$=NULL; };

_elsif_lst_		:	Keyword_ELSIF OpenBracket_ROUND _expr_ CloseBracket_ROUND OpenBracket_BODY _decl_lst_ CloseBracket_BODY _elsif_lst_
						{
						$$=treeId2Alloc(E_STM_IFEXPRBODY,$3,$6,&@1);
						$$->next=$8;
						}|
					/* epsilon */
						{ $$=NULL; };

_else_			:	Keyword_ELSE OpenBracket_BODY _decl_lst_ CloseBracket_BODY
						{ $$=$3; }|
					/* epsilon */
						{ $$=NULL; }

_expr_			:	OpenBracket_ROUND _expr_ CloseBracket_ROUND
						{ $$=$2; }|
					UnaryOperator_NOT _expr_
						{ $$=treeId1Alloc(E_EXPR_NOT,$2,&@1); }|
					UnaryOperator_COM _expr_
						{ $$=treeId1Alloc(E_EXPR_COM,$2,&@1); }|
					DualOperator_SUB _expr_ %prec UnaryOperator_SUB
						{ $$=treeId1Alloc(E_EXPR_NEG,$2,&@1); }|
					Keyword_B2W OpenBracket_ROUND _expr_ CloseBracket_ROUND
						{ $$=treeId1Alloc(E_EXPR_B2W,$3,&@1); }|
					Keyword_B2DW OpenBracket_ROUND _expr_ CloseBracket_ROUND
						{ $$=treeId1Alloc(E_EXPR_B2DW,$3,&@1); }|
					Keyword_W2B OpenBracket_ROUND _expr_ CloseBracket_ROUND
						{ $$=treeId1Alloc(E_EXPR_W2B,$3,&@1); }|
					Keyword_W2DW OpenBracket_ROUND _expr_ CloseBracket_ROUND
						{ $$=treeId1Alloc(E_EXPR_W2DW,$3,&@1); }|
					Keyword_DW2B OpenBracket_ROUND _expr_ CloseBracket_ROUND
						{ $$=treeId1Alloc(E_EXPR_DW2B,$3,&@1); }|
					Keyword_DW2W OpenBracket_ROUND _expr_ CloseBracket_ROUND
						{ $$=treeId1Alloc(E_EXPR_DW2W,$3,&@1); }|
					_expr_ DualOperator_MUL _expr_
						{ $$=treeId2Alloc(E_EXPR_MUL,$1,$3,&@1); }|
					_expr_ DualOperator_DIV _expr_
						{ $$=treeId2Alloc(E_EXPR_DIV,$1,$3,&@1); }|
					_expr_ DualOperator_ADD _expr_
						{ $$=treeId2Alloc(E_EXPR_ADD,$1,$3,&@1); }|
					_expr_ DualOperator_SUB _expr_
						{ $$=treeId2Alloc(E_EXPR_SUB,$1,$3,&@1); }|
					_expr_ DualOperator_SHL _expr_
						{ $$=treeId2Alloc(E_EXPR_SHL,$1,$3,&@1); }|
					_expr_ DualOperator_SHR _expr_
						{ $$=treeId2Alloc(E_EXPR_SHR,$1,$3,&@1); }|
					_expr_ DualOperator_LT _expr_
						{ $$=treeId2Alloc(E_EXPR_LT,$1,$3,&@1); }|
					_expr_ DualOperator_LTE _expr_
						{ $$=treeId2Alloc(E_EXPR_LTE,$1,$3,&@1); }|
					_expr_ DualOperator_GT _expr_
						{ $$=treeId2Alloc(E_EXPR_GT,$1,$3,&@1); }|
					_expr_ DualOperator_GTE _expr_
						{ $$=treeId2Alloc(E_EXPR_GTE,$1,$3,&@1); }|
					_expr_ DualOperator_NEQ _expr_
						{ $$=treeId2Alloc(E_EXPR_NEQ,$1,$3,&@1); }|
					_expr_ DualOperator_EQ _expr_
						{ $$=treeId2Alloc(E_EXPR_EQ,$1,$3,&@1); }|
					_expr_ DualOperator_AND _expr_
						{ $$=treeId2Alloc(E_EXPR_AND,$1,$3,&@1); }|
					_expr_ DualOperator_OR _expr_
						{ $$=treeId2Alloc(E_EXPR_OR,$1,$3,&@1); }|
					_expr_ DualOperator_XOR _expr_
						{ $$=treeId2Alloc(E_EXPR_XOR,$1,$3,&@1); }|
					Value_DWORD
						{ $$=$1; }|
					Value_WORD
						{ $$=$1; }|
					Value_BYTE
						{ $$=$1; }|
					_var_
						{ $$=treeId1Alloc(E_EXPR_VAR,$1,&@1); };

_var_			:	Value_STRING _var_sub_
						{
						if($2)
							{
							$$=$2;
							$$->last->next=treeId1Alloc(E_VAR_ROOT,$1,&@1);
							}
						else
							{ $$=treeId1Alloc(E_VAR_ROOT,$1,&@1); }
						};

_var_sub_		:	Separator_SELECT Value_INUM _var_sub_
						{
						if($3)
							{
							valueLeaf	*tmp=treeId1Alloc(E_VAR_STRUCT,$2,&@1);

							$$=$3;
							$$->last->next=tmp;
							$$->last=tmp;
							}
						else
							{
							$$=treeId1Alloc(E_VAR_STRUCT,$2,&@1);
							$$->last=$$;
							}
						}|
					OpenBracket_SQUARE _expr_ CloseBracket_SQUARE _var_sub_
						{
						if($4)
							{
							valueLeaf	*tmp=treeId1Alloc(E_VAR_ARRAY,$2,&@1);

							$$=$4;
							$$->last->next=tmp;
							$$->last=tmp;
							}
						else
							{
							$$=treeId1Alloc(E_VAR_ARRAY,$2,&@1);
							$$->last=$$;
							}
						}|
					/* epsilon */
						{ $$=NULL; };

/* ************************************************************************* */

%%

void yyerror(const YYLTYPE *locp,void *p,char const *msg)
{
	if(locp->first_line>=0)
		{ printf("%s:%d,%d\tParsError: %s%c",locp->source,locp->first_line,locp->first_column,msg,SEP); }
	else
		{ printf(":0,0\tParsError: %s%c",msg,SEP); }

	numErr++;

	return;
}

valueLeaf	*treeAlloc(\
				vEnum id,\
				_DWORD_ dwordValue,\
				_WORD_ wordValue,\
				_BYTE_ byteValue,\
				unsigned long int inumValue,\
				char *stringValue,\
				valueLeaf *param1,\
				valueLeaf *param2,\
				valueLeaf *param3,\
				const YYLTYPE *locp)
{
	valueLeaf	*tmp;

	if(!(tmp=(valueLeaf *) myMalloc(sizeof(valueLeaf))))
		{
		printf("[%s:%d] ParsError:OutOfMemory%c",__FILE__,__LINE__,SEP);
		exit(ERR_EXIT);
		}

	memset(tmp,0,sizeof(valueLeaf));

	tmp->id=id;
	tmp->dwordValue=dwordValue;
	tmp->wordValue=wordValue;
	tmp->byteValue=byteValue;
	tmp->inumValue=inumValue;
	tmp->stringValue=stringValue;
	tmp->param1=param1;
	tmp->param2=param2;
	tmp->param3=param3;

	return(tmp);
}

valueLeaf *treeDwordAlloc(_DWORD_ dwordValue,const YYLTYPE *locp)
{ return(treeAlloc(E_VALUE_DWORD,dwordValue,0,0,0,NULL,NULL,NULL,NULL,locp)); }

valueLeaf *treeWordAlloc(_WORD_ wordValue,const YYLTYPE *locp)
{ return(treeAlloc(E_VALUE_WORD,0,wordValue,0,0,NULL,NULL,NULL,NULL,locp)); }

valueLeaf *treeByteAlloc(_BYTE_ byteValue,const YYLTYPE *locp)
{ return(treeAlloc(E_VALUE_BYTE,0,0,byteValue,0,NULL,NULL,NULL,NULL,locp)); }

valueLeaf *treeInumAlloc(unsigned long int inumValue,const YYLTYPE *locp)
{ return(treeAlloc(E_VALUE_INUM,0,0,0,inumValue,NULL,NULL,NULL,NULL,locp)); }

valueLeaf *treeStringAlloc(char *stringValue,const YYLTYPE *locp)
{ return(treeAlloc(E_VALUE_STRING,0,0,0,0,stringValue,NULL,NULL,NULL,locp)); }

valueLeaf *treeId0Alloc(vEnum id,const YYLTYPE *locp)
{ return(treeAlloc(id,0,0,0,0,NULL,NULL,NULL,NULL,locp)); }

valueLeaf *treeId1Alloc(vEnum id,valueLeaf *param1,const YYLTYPE *locp)
{ return(treeAlloc(id,0,0,0,0,NULL,param1,NULL,NULL,locp)); }

valueLeaf *treeId2Alloc(vEnum id,valueLeaf *param1,valueLeaf *param2,const YYLTYPE *locp)
{ return(treeAlloc(id,0,0,0,0,NULL,param1,param2,NULL,locp)); }

valueLeaf *treeId3Alloc(vEnum id,valueLeaf *param1,valueLeaf *param2,valueLeaf *param3,const YYLTYPE *locp)
{ return(treeAlloc(id,0,0,0,0,NULL,param1,param2,param3,locp)); }

/* riconoscimento token da input */
int yylex(YYSTYPE *lvalp,YYLTYPE *llocp,void *p)
{
	char	bufLine[256];
	char	bufToken[256];
	char	bufString[256];
	char	*tmp1,*tmp2;

	/* riconoscimento di source:linea,colonna */
	fscanf(stdin,"%s%s%s\n",bufLine,bufToken,bufString,SEP);

	if(!strcmp(bufToken,"ERR"))
		{
		printf("%s\t%s%c",bufLine,bufString,SEP);
		exit(ERR_EXIT);
		}

	for(tmp1=bufLine;*tmp1!=':';tmp1++);
	*tmp1=0;

	for(tmp2=tmp1+1;*tmp2!=',';tmp2++);
	*tmp2=0;

	llocp->first_line=llocp->last_line=atoi(tmp1+1);
	llocp->first_column=llocp->last_column=atoi(tmp2+1);

	if(!(llocp->source=(char *) myMalloc(strlen(bufLine)+1)))
		{
		printf("[%s:%d] ParsError:OutOfMemory%c",__FILE__,__LINE__,SEP);
		exit(ERR_EXIT);
		}

	*llocp->source=0;
	strcpy(llocp->source,bufLine);

	*tmp1=':';
	*tmp2=',';

	/* analisi */
	if(!strcmp(bufToken,"OK"))
		{
		root.source=llocp->source;
		root.fileLine=llocp->first_line;
		root.fileRow=llocp->first_column;

		return yylex(lvalp,llocp,p);
		}
	else if(!strcmp(bufToken,"EOF"))
		{ return(0); }

	/* categoria keyword */
	if(!strcmp(bufToken,"KEW"))
		{
		if(!strcmp(bufString,"struct"))
			{ return(Keyword_STRUCT); }
		else if(!strcmp(bufString,"array"))
			{ return(Keyword_ARRAY); }
		else if(!strcmp(bufString,"of"))
			{ return(Keyword_OF); }
		else if(!strcmp(bufString,"if"))
			{ return(Keyword_IF); }
		else if(!strcmp(bufString,"elsif"))
			{ return(Keyword_ELSIF); }
		else if(!strcmp(bufString,"else"))
			{ return(Keyword_ELSE); }
		else if(!strcmp(bufString,"while"))
			{ return(Keyword_WHILE); }
		else if(!strcmp(bufString,"const"))
			{ return(Keyword_CONST); }
		else if(!strcmp(bufString,"b2w"))
			{ return(Keyword_B2W); }
		else if(!strcmp(bufString,"b2dw"))
			{ return(Keyword_B2DW); }
		else if(!strcmp(bufString,"w2b"))
			{ return(Keyword_W2B); }
		else if(!strcmp(bufString,"w2dw"))
			{ return(Keyword_W2DW); }
		else if(!strcmp(bufString,"dw2b"))
			{ return(Keyword_DW2B); }
		else if(!strcmp(bufString,"dw2w"))
			{ return(Keyword_DW2W); }
		else
			{
			printf("%s\tParsError:UnknownKeywordToken(%s)%c",bufLine,bufString,SEP);
			exit(ERR_EXIT);
			}
		}
	/* categoria tipo nativo */
	else if(!strcmp(bufToken,"TYP"))
		{
		if(!strcmp(bufString,"dword"))
			{ return(Type_DWORD); }
		else if(!strcmp(bufString,"word"))
			{ return(Type_WORD); }
		else if(!strcmp(bufString,"byte"))
			{ return(Type_BYTE); }
		else
			{
			printf("%s\tParsError:UnknownTypeToken(%s)%c",bufLine,bufString,SEP);
			exit(ERR_EXIT);
			}
		}
	/* categoria parentesi */
	else if(!strcmp(bufToken,"BRK"))
		{
		if(!strcmp(bufString,"{"))
			{ return(OpenBracket_BODY); }
		else if(!strcmp(bufString,"}"))
			{ return(CloseBracket_BODY); }
		else if(!strcmp(bufString,"["))
			{ return(OpenBracket_SQUARE); }
		else if(!strcmp(bufString,"]"))
			{ return(CloseBracket_SQUARE); }
		else if(!strcmp(bufString,"("))
			{ return(OpenBracket_ROUND); }
		else if(!strcmp(bufString,")"))
			{ return(CloseBracket_ROUND); }
		else
			{
			printf("%s\tParsError:UnknownBracketToken(%s)%c",bufLine,bufString,SEP);
			exit(ERR_EXIT);
			}
		}
	/* categoria operatore unario */
	else if(!strcmp(bufToken,"MOP"))
		{
		if(!strcmp(bufString,"!"))
			{ return(UnaryOperator_NOT); }
		else if(!strcmp(bufString,"~"))
			{ return(UnaryOperator_COM); }
		else
			{
			printf("%s\tParsError:UnknownUnaryOperatorToken(%s)%c",bufLine,bufString,SEP);
			exit(ERR_EXIT);
			}
		}
	/* categoria operatore duale */
	else if(!strcmp(bufToken,"DOP"))
		{
		if(!strcmp(bufString,"&"))
			{ return(DualOperator_AND); }
		else if(!strcmp(bufString,"|"))
			{ return(DualOperator_OR); }
		else if(!strcmp(bufString,"^"))
			{ return(DualOperator_XOR); }
		else if(!strcmp(bufString,"+"))
			{ return(DualOperator_ADD); }
		else if(!strcmp(bufString,"-"))
			{ return(DualOperator_SUB); }
		else if(!strcmp(bufString,"*"))
			{ return(DualOperator_MUL); }
		else if(!strcmp(bufString,"/"))
			{ return(DualOperator_DIV); }
		else if(!strcmp(bufString,"!="))
			{ return(DualOperator_NEQ); }
		else if(!strcmp(bufString,"=="))
			{ return(DualOperator_EQ); }
		else if(!strcmp(bufString,"<"))
			{ return(DualOperator_LT); }
		else if(!strcmp(bufString,">"))
			{ return(DualOperator_GT); }
		else if(!strcmp(bufString,"<="))
			{ return(DualOperator_LTE); }
		else if(!strcmp(bufString,">="))
			{ return(DualOperator_GTE); }
		else if(!strcmp(bufString,">>"))
			{ return(DualOperator_SHR); }
		else if(!strcmp(bufString,"<<"))
			{ return(DualOperator_SHL); }
		else if(!strcmp(bufString,"="))
			{ return(DualOperator_ASG); }
		else
			{
			printf("%s\tParsError:UnknownDualOperatorToken(%s)%c",bufLine,bufString,SEP);
			exit(ERR_EXIT);
			}
		}
	/* categoria separatore */
	else if(!strcmp(bufToken,"SEP"))
		{
		if(!strcmp(bufString,";"))
			{ return(Separator_COLUMN); }
		else if(!strcmp(bufString,"."))
			{ return(Separator_SELECT); }
		else if(!strcmp(bufString,","))
			{ return(Separator_COMMA); }
		else
			{
			printf("%s\tParsError:UnknownSeparatorToken(%s)%c",bufLine,bufString,SEP);
			exit(ERR_EXIT);
			}
		}
	/* categoria dword */
	else if(!strcmp(bufToken,"W32"))
		{
		unsigned long int	tmpI;

		if(sscanf(bufString,"0x%lx",&tmpI)==1)
			{
			*lvalp=treeDwordAlloc((_DWORD_) (tmpI&0xFFFFFFFF),llocp);
			return(Value_DWORD);
			}
		else
			{
			printf("%s\tParsError:UnknownIntToken(%s)%c",bufLine,bufString,SEP);
			exit(ERR_EXIT);
			}
		}
	/* categoria word */
	else if(!strcmp(bufToken,"W16"))
		{
		unsigned long int	tmpI;

		if(sscanf(bufString,"0x%lx",&tmpI)==1)
			{
			*lvalp=treeWordAlloc((_WORD_) (tmpI&0xFFFF),llocp);
			return(Value_WORD);
			}
		else
			{
			printf("%s\tParsError:UnknownIntToken(%s)%c",bufLine,bufString,SEP);
			exit(ERR_EXIT);
			}
		}
	/* categoria byte */
	else if(!strcmp(bufToken,"BY8"))
		{
		unsigned long int	tmpI;

		if(sscanf(bufString,"0x%lx",&tmpI)==1)
			{
			*lvalp=treeByteAlloc((_BYTE_) (tmpI&0xFF),llocp);
			return(Value_BYTE);
			}
		else
			{
			printf("%s\tParsError:UnknownIntToken(%s)%c",bufLine,bufString,SEP);
			exit(ERR_EXIT);
			}
		}
	/* categoria numero intero */
	else if(!strcmp(bufToken,"INU"))
		{
		unsigned long int	tmpI;

		if(sscanf(bufString,"%lu",&tmpI)==1)
			{
			*lvalp=treeInumAlloc(tmpI,llocp);
			return(Value_INUM);
			}
		else
			{
			printf("%s\tParsError:UnknownIntToken(%s)%c",bufLine,bufString,SEP);
			exit(ERR_EXIT);
			}
		}
	/* categoria ID == stringa */
	else if(!strcmp(bufToken,"IID"))
		{
		char		*tmpS;

		if(!(tmpS=(char *) myMalloc(strlen(bufString)+1)))
			{
			printf("[%s:%d] ParsError:OutOfMemory%c",__FILE__,__LINE__,SEP);
			exit(ERR_EXIT);
			}

		*tmpS=0;
		strcpy(tmpS,bufString);

		*lvalp=treeStringAlloc(tmpS,llocp);
		return(Value_STRING);
		}
	else
		{
		printf("%s\tParsError:UnknownToken(%s)%c",bufLine,bufString,SEP);
		exit(ERR_EXIT);
		}
}

void usage(char *name)
{
	printf("\nC Parser - Cosimo Oliboni\n\n");
	printf("\"%s\" parsing da stdin\n\n",name);

	return;
}

/* *************************** gestione degli user type *********** */

int eqUserType(valueLeaf *type1,valueLeaf *type2)
{
	valueLeaf	*tmp1,*tmp2;

	if(type1->id!=type2->id)
		{ return(0); }

	switch(type1->id)
		{
		case E_TYPE_DWORD:
		case E_TYPE_WORD:
		case E_TYPE_BYTE:
			return(1);

		case E_TYPE_ARRAY:
			if(type1->param1->inumValue!=type2->param1->inumValue)
				{ return(0); }

			return(eqUserType(type1->param2,type2->param2));

		case E_TYPE_STRUCT:
			tmp1=type1->param1;
			tmp2=type2->param1;

			while(tmp1&&tmp2)
				{
				if(!eqUserType(tmp1,tmp2))
					{ return(0); }

				tmp1=tmp1->next;
				tmp2=tmp2->next;
				}

			return(!(tmp1||tmp2));

		/* dummy */
		default:
			return(0);
		}
}

int getUserType(valueLeaf *type,valueLeaf **res)
{
	valueLeaf	*tmpRes=typeRoot;
	valueLeaf	*lastRes;
	int			index=1;

	while(tmpRes)
		{
		if(eqUserType(type,tmpRes))
			{
			if(res)
				{ *res=tmpRes; }
			return(index);
			}

		lastRes=tmpRes;
		tmpRes=tmpRes->next;
		index++;
		}

	if(res)
		{ *res=lastRes; }
	return(0);
}

void createUserType(valueLeaf *type)
{
	if(!typeRoot)
		{
		if(!(typeRoot=(valueLeaf *) myMalloc(sizeof(valueLeaf))))
			{
			printf("[%s:%d] ParsError:OutOfMemory%c",__FILE__,__LINE__,SEP);
			exit(ERR_EXIT);
			}

		memcpy(typeRoot,type,sizeof(valueLeaf));
		typeRoot->next=NULL;
		}
	else
		{
		valueLeaf	*res;

		if(!getUserType(type,&res))
			{
			if(!(res->next=(valueLeaf *) myMalloc(sizeof(valueLeaf))))
				{
				printf("[%s:%d] ParsError:OutOfMemory%c",__FILE__,__LINE__,SEP);
				exit(ERR_EXIT);
				}

			memcpy(res->next,type,sizeof(valueLeaf));
			res->next->next=NULL;
			}
		}
}

/* *************************** prettyPrint ************************ */

void prettyPrintString(char *str)
{
	printf("([");

	while(*str)
		{
		printf("ch_%c",*str);

		if(*(str+1))
			{ printf(";"); }

		str++;
		}

	printf("])");
}

void prettyPrintByte(_BYTE_ num)
{
	printf("(\\langle x%1X,x%1X \\rangle)",(unsigned int) (num>>4),(unsigned int) (num&0xF));
}

void prettyPrintWord(_WORD_ num)
{
	printf("(\\langle \\langle x%1X,x%1X \\rangle : \\langle x%1X,x%1X \\rangle \\rangle)",\
		(unsigned int) (num>>12),(unsigned int) ((num>>8)&0xF),\
		(unsigned int) ((num>>4)&0xF),(unsigned int) (num&0xF));
}

void prettyPrintDword(_DWORD_ num)
{
	printf("(\\langle \\langle \\langle x%1X,x%1X \\rangle : \\langle x%1X,x%1X \\rangle \\rangle . \\langle \\langle x%1X,x%1X \\rangle : \\langle x%1X,x%1X \\rangle \\rangle \\rangle)",\
		(unsigned int) (num>>28),(unsigned int) ((num>>24)&0xF),\
		(unsigned int) ((num>>20)&0xF),(unsigned int) ((num>>16)&0xF),\
		(unsigned int) ((num>>12)&0xF),(unsigned int) ((num>>8)&0xF),\
		(unsigned int) ((num>>4)&0xF),(unsigned int) (num&0xF));
}

void prettyPrintIndent(int indent)
{
	int	index;

	for(index=0;index<indent;index++)
		{ printf(" "); }
}

void prettyPrintInum(unsigned long int num)
{
	if(!num)
		{ printf("O\n"); }
	else
		{ printf("%lu\n",num); }
}

void prettyPrintInit(valueLeaf *cur,int indent)
{
	if(cur->id==E_VALUE_BYTE)
		{ prettyPrintIndent(indent); printf("(PREAST_INIT_VAL_BYTE8 "); prettyPrintByte(cur->byteValue); printf(")\n"); }
	else if(cur->id==E_VALUE_WORD)
		{ prettyPrintIndent(indent); printf("(PREAST_INIT_VAL_WORD16 "); prettyPrintWord(cur->wordValue); printf(")\n"); }
	else if(cur->id==E_VALUE_DWORD)
		{ prettyPrintIndent(indent); printf("(PREAST_INIT_VAL_WORD32 "); prettyPrintDword(cur->dwordValue); printf(")\n"); }
	else if(cur->id==E_VALUE_ARRAY)
		{
		valueLeaf	*tmp=cur->param1;

		prettyPrintIndent(indent); printf("(PREAST_INIT_VAL_ARRAY\n");

		prettyPrintIndent(indent+1); printf("(\\laquo\n");
		if(!tmp->next)
			{ prettyPrintIndent(indent+2); printf("£\n"); }
		while(tmp)
			{
			prettyPrintInit(tmp,indent+2);

			if(tmp->next)
				{
				if(tmp->next->next)
					{ prettyPrintIndent(indent+2); printf(";\n"); }
				else
					{ prettyPrintIndent(indent+2); printf("£\n"); }
				}

			tmp=tmp->next;
			}
		prettyPrintIndent(indent+1); printf("\\raquo)\n");

		prettyPrintIndent(indent); printf(")\n");
		}
	else if(cur->id==E_VALUE_STRUCT)
		{
		valueLeaf	*tmp=cur->param1;

		prettyPrintIndent(indent); printf("(PREAST_INIT_VAL_STRUCT\n");

		prettyPrintIndent(indent+1); printf("(\\laquo\n");
		if(!tmp->next)
			{ prettyPrintIndent(indent+2); printf("£\n"); }
		while(tmp)
			{
			prettyPrintInit(tmp,indent+2);

			if(tmp->next)
				{
				if(tmp->next->next)
					{ prettyPrintIndent(indent+2); printf(";\n"); }
				else
					{ prettyPrintIndent(indent+2); printf("£\n"); }
				}

			tmp=tmp->next;
			}
		prettyPrintIndent(indent+1); printf("\\raquo)\n");

		prettyPrintIndent(indent); printf(")\n");
		}
}

void prettyPrintBody(valueLeaf *cur,int indent)
{
	if(!cur)
		{ prettyPrintIndent(indent); printf("(PREAST_NO_DECL [])\n"); }
	else if((cur->id==E_DECL_CONST)||(cur->id==E_DECL_VAR))
		{ prettyPrint(cur,indent); }
	else
		{
		valueLeaf	*tmp=cur;

		prettyPrintIndent(indent); printf("(PREAST_NO_DECL\n");

		prettyPrintIndent(indent+1); printf("[\n");
		while(tmp)
			{
			prettyPrint(tmp,indent+2);

			if(tmp->next)
				{ prettyPrintIndent(indent+2); printf(";\n"); }

			tmp=tmp->next;
			}
		prettyPrintIndent(indent+1); printf("]\n");

		prettyPrintIndent(indent); printf(")\n");
		}

}

void prettyPrint(valueLeaf *cur,int indent)
{
	/* ** misc ** */
	if(cur->id==E_VALUE_STRING)
		{ prettyPrintIndent(indent); prettyPrintString(cur->stringValue); printf("\n"); }
	else if(cur->id==E_VALUE_INUM)
		{ prettyPrintIndent(indent); prettyPrintInum(cur->inumValue); }

	/* ** tipi ** */
	else if(cur->id==E_TYPE_BYTE)
		{ prettyPrintIndent(indent); printf("(AST_TYPE_BASE AST_BASE_TYPE_BYTE8)\n"); }
	else if(cur->id==E_TYPE_WORD)
		{ prettyPrintIndent(indent); printf("(AST_TYPE_BASE AST_BASE_TYPE_WORD16)\n"); }
	else if(cur->id==E_TYPE_DWORD)
		{ prettyPrintIndent(indent); printf("(AST_TYPE_BASE AST_BASE_TYPE_WORD32)\n"); }
	else if(cur->id==E_TYPE_ARRAY)
		{
		prettyPrintIndent(indent); printf("(AST_TYPE_ARRAY\n");
		prettyPrint(cur->param2,indent+1);	//type
		prettyPrint(cur->param1,indent+1);	//size
		prettyPrintIndent(indent); printf(")\n");
		}
	else if(cur->id==E_TYPE_STRUCT)
		{
		valueLeaf	*tmp=cur->param1;

		prettyPrintIndent(indent); printf("(AST_TYPE_STRUCT\n");

		prettyPrintIndent(indent+1); printf("(\\laquo\n");
		if(!tmp->next)
			{ prettyPrintIndent(indent+2); printf("£\n"); }
		while(tmp)
			{
			prettyPrint(tmp,indent+2);

			if(tmp->next)
				{
				if(tmp->next->next)
					{ prettyPrintIndent(indent+2); printf(";\n"); }
				else
					{ prettyPrintIndent(indent+2); printf("£\n"); }
				}

			tmp=tmp->next;
			}
		prettyPrintIndent(indent+1); printf("\\raquo)\n");

		prettyPrintIndent(indent); printf(")\n");
		}
	
	/* ** valori come espressioni ** */
	else if(cur->id==E_VALUE_BYTE)
		{ prettyPrintIndent(indent); printf("(PREAST_EXPR_BYTE8 "); prettyPrintByte(cur->byteValue); printf(")\n"); }
	else if(cur->id==E_VALUE_WORD)
		{ prettyPrintIndent(indent); printf("(PREAST_EXPR_WORD16 "); prettyPrintWord(cur->wordValue); printf(")\n"); }
	else if(cur->id==E_VALUE_DWORD)
		{ prettyPrintIndent(indent); printf("(PREAST_EXPR_WORD32 "); prettyPrintDword(cur->dwordValue); printf(")\n"); }

	/* ** variabili */
	else if(cur->id==E_VAR_ROOT)
		{ prettyPrintIndent(indent); printf("(PREAST_VAR_ID "); prettyPrintString(cur->param1->stringValue); printf(")\n"); }
	else if(cur->id==E_VAR_STRUCT)
		{
		prettyPrintIndent(indent); printf("(PREAST_VAR_STRUCT\n");
		prettyPrint(cur->next,indent+1);
		prettyPrint(cur->param1,indent+1);
		prettyPrintIndent(indent); printf(")\n");
		}
	else if(cur->id==E_VAR_ARRAY)
		{
		prettyPrintIndent(indent); printf("(PREAST_VAR_ARRAY\n");
		prettyPrint(cur->next,indent+1);
		prettyPrint(cur->param1,indent+1);
		prettyPrintIndent(indent); printf(")\n");
		}

	/* ** espressioni ** */
	else if(cur->id==E_EXPR_VAR)
		{
		prettyPrintIndent(indent); printf("(PREAST_EXPR_ID\n");
		prettyPrint(cur->param1,indent+1);
		prettyPrintIndent(indent); printf(")\n");
		}
	else if(cur->id==E_EXPR_NOT)
		{
		prettyPrintIndent(indent); printf("(PREAST_EXPR_NOT\n");
		prettyPrint(cur->param1,indent+1);
		prettyPrintIndent(indent); printf(")\n");
		}
	else if(cur->id==E_EXPR_COM)
		{
		prettyPrintIndent(indent); printf("(PREAST_EXPR_COM\n");
		prettyPrint(cur->param1,indent+1);
		prettyPrintIndent(indent); printf(")\n");
		}
	else if(cur->id==E_EXPR_NEG)
		{
		prettyPrintIndent(indent); printf("(PREAST_EXPR_NEG\n");
		prettyPrint(cur->param1,indent+1);
		prettyPrintIndent(indent); printf(")\n");
		}
	else if(cur->id==E_EXPR_B2W)
		{
		prettyPrintIndent(indent); printf("(PREAST_EXPR_B8toW16\n");
		prettyPrint(cur->param1,indent+1);
		prettyPrintIndent(indent); printf(")\n");
		}
	else if(cur->id==E_EXPR_B2DW)
		{
		prettyPrintIndent(indent); printf("(PREAST_EXPR_B8toW32\n");
		prettyPrint(cur->param1,indent+1);
		prettyPrintIndent(indent); printf(")\n");
		}
	else if(cur->id==E_EXPR_W2B)
		{
		prettyPrintIndent(indent); printf("(PREAST_EXPR_W16toB8\n");
		prettyPrint(cur->param1,indent+1);
		prettyPrintIndent(indent); printf(")\n");
		}
	else if(cur->id==E_EXPR_W2DW)
		{
		prettyPrintIndent(indent); printf("(PREAST_EXPR_W16toW32\n");
		prettyPrint(cur->param1,indent+1);
		prettyPrintIndent(indent); printf(")\n");
		}
	else if(cur->id==E_EXPR_DW2B)
		{
		prettyPrintIndent(indent); printf("(PREAST_EXPR_W32toB8\n");
		prettyPrint(cur->param1,indent+1);
		prettyPrintIndent(indent); printf(")\n");
		}
	else if(cur->id==E_EXPR_DW2W)
		{
		prettyPrintIndent(indent); printf("(PREAST_EXPR_W32toW16\n");
		prettyPrint(cur->param1,indent+1);
		prettyPrintIndent(indent); printf(")\n");
		}
	else if(cur->id==E_EXPR_ADD)
		{
		prettyPrintIndent(indent); printf("(PREAST_EXPR_ADD\n");
		prettyPrint(cur->param1,indent+1);
		prettyPrint(cur->param2,indent+1);
		prettyPrintIndent(indent); printf(")\n");
		}
	else if(cur->id==E_EXPR_SUB)
		{
		prettyPrintIndent(indent); printf("(PREAST_EXPR_SUB\n");
		prettyPrint(cur->param1,indent+1);
		prettyPrint(cur->param2,indent+1);
		prettyPrintIndent(indent); printf(")\n");
		}
	else if(cur->id==E_EXPR_MUL)
		{
		prettyPrintIndent(indent); printf("(PREAST_EXPR_MUL\n");
		prettyPrint(cur->param1,indent+1);
		prettyPrint(cur->param2,indent+1);
		prettyPrintIndent(indent); printf(")\n");
		}
	else if(cur->id==E_EXPR_DIV)
		{
		prettyPrintIndent(indent); printf("(PREAST_EXPR_DIV\n");
		prettyPrint(cur->param1,indent+1);
		prettyPrint(cur->param2,indent+1);
		prettyPrintIndent(indent); printf(")\n");
		}
	else if(cur->id==E_EXPR_SHL)
		{
		prettyPrintIndent(indent); printf("(PREAST_EXPR_SHL\n");
		prettyPrint(cur->param1,indent+1);
		prettyPrint(cur->param2,indent+1);
		prettyPrintIndent(indent); printf(")\n");
		}
	else if(cur->id==E_EXPR_SHR)
		{
		prettyPrintIndent(indent); printf("(PREAST_EXPR_SHR\n");
		prettyPrint(cur->param1,indent+1);
		prettyPrint(cur->param2,indent+1);
		prettyPrintIndent(indent); printf(")\n");
		}
	else if(cur->id==E_EXPR_AND)
		{
		prettyPrintIndent(indent); printf("(PREAST_EXPR_AND\n");
		prettyPrint(cur->param1,indent+1);
		prettyPrint(cur->param2,indent+1);
		prettyPrintIndent(indent); printf(")\n");
		}
	else if(cur->id==E_EXPR_OR)
		{
		prettyPrintIndent(indent); printf("(PREAST_EXPR_OR\n");
		prettyPrint(cur->param1,indent+1);
		prettyPrint(cur->param2,indent+1);
		prettyPrintIndent(indent); printf(")\n");
		}
	else if(cur->id==E_EXPR_XOR)
		{
		prettyPrintIndent(indent); printf("(PREAST_EXPR_XOR\n");
		prettyPrint(cur->param1,indent+1);
		prettyPrint(cur->param2,indent+1);
		prettyPrintIndent(indent); printf(")\n");
		}
	else if(cur->id==E_EXPR_LT)
		{
		prettyPrintIndent(indent); printf("(PREAST_EXPR_LT\n");
		prettyPrint(cur->param1,indent+1);
		prettyPrint(cur->param2,indent+1);
		prettyPrintIndent(indent); printf(")\n");
		}
	else if(cur->id==E_EXPR_LTE)
		{
		prettyPrintIndent(indent); printf("(PREAST_EXPR_LTE\n");
		prettyPrint(cur->param1,indent+1);
		prettyPrint(cur->param2,indent+1);
		prettyPrintIndent(indent); printf(")\n");
		}
	else if(cur->id==E_EXPR_GT)
		{
		prettyPrintIndent(indent); printf("(PREAST_EXPR_GT\n");
		prettyPrint(cur->param1,indent+1);
		prettyPrint(cur->param2,indent+1);
		prettyPrintIndent(indent); printf(")\n");
		}
	else if(cur->id==E_EXPR_GTE)
		{
		prettyPrintIndent(indent); printf("(PREAST_EXPR_GTE\n");
		prettyPrint(cur->param1,indent+1);
		prettyPrint(cur->param2,indent+1);
		prettyPrintIndent(indent); printf(")\n");
		}
	else if(cur->id==E_EXPR_EQ)
		{
		prettyPrintIndent(indent); printf("(PREAST_EXPR_EQ\n");
		prettyPrint(cur->param1,indent+1);
		prettyPrint(cur->param2,indent+1);
		prettyPrintIndent(indent); printf(")\n");
		}
	else if(cur->id==E_EXPR_NEQ)
		{
		prettyPrintIndent(indent); printf("(PREAST_EXPR_NEQ\n");
		prettyPrint(cur->param1,indent+1);
		prettyPrint(cur->param2,indent+1);
		prettyPrintIndent(indent); printf(")\n");
		}

	/* ** dichiarazioni ** */
	else if(cur->id==E_DECL_CONST)
		{
		prettyPrintIndent(indent); printf("(PREAST_CONST_DECL\n");
		prettyPrint(cur->param2,indent+1);	//string
		prettyPrint(cur->param1,indent+1);	//type
		
		if((cur->param3->id==E_VAR_ROOT)||(cur->param3->id==E_VAR_STRUCT)||(cur->param3->id==E_VAR_ARRAY))
			{
			prettyPrintIndent(indent+1); printf("(PREAST_INIT_VAR\n");
			prettyPrint(cur->param3,indent+2);	//init
			prettyPrintIndent(indent+1); printf(")\n");
			}
		else
			{
			prettyPrintIndent(indent+1); printf("(PREAST_INIT_VAL\n");
			prettyPrintInit(cur->param3,indent+2);	//init
			prettyPrintIndent(indent+1); printf(")\n");
			}

		if(cur->next)
			{
			if((cur->next->id==E_DECL_CONST)||(cur->next->id==E_DECL_VAR))
				{ prettyPrint(cur->next,indent+1); }	//next decl
			else
				{
				valueLeaf	*tmp=cur->next;

				prettyPrintIndent(indent+1); printf("(PREAST_NO_DECL\n");

				prettyPrintIndent(indent+2); printf("[\n");
				while(tmp)
					{
					prettyPrint(tmp,indent+3);

					if(tmp->next)
						{ prettyPrintIndent(indent+3); printf(";\n"); }

					tmp=tmp->next;
					}
				prettyPrintIndent(indent+2); printf("]\n");

				prettyPrintIndent(indent+1); printf(")\n");
				}
			}
		else
			{ prettyPrintIndent(indent+1); printf("(PREAST_NO_DECL [])\n"); }
		

		prettyPrintIndent(indent); printf(")\n");
		}
	else if(cur->id==E_DECL_VAR)
		{
		prettyPrintIndent(indent); printf("(PREAST_VAR_DECL\n");
		prettyPrint(cur->param2,indent+1);	//string
		prettyPrint(cur->param1,indent+1);	//type
		
		if(cur->param3)
			{
			prettyPrintIndent(indent+1); printf("(Some ?\n");

			if((cur->param3->id==E_VAR_ROOT)||(cur->param3->id==E_VAR_STRUCT)||(cur->param3->id==E_VAR_ARRAY))
				{
				prettyPrintIndent(indent+2); printf("(PREAST_INIT_VAR\n");
				prettyPrint(cur->param3,indent+3);	//init
				prettyPrintIndent(indent+2); printf(")\n");
				}
			else
				{
				prettyPrintIndent(indent+2); printf("(PREAST_INIT_VAL\n");
				prettyPrintInit(cur->param3,indent+3);	//init
				prettyPrintIndent(indent+2); printf(")\n");
				}

			prettyPrintIndent(indent+1); printf(")\n");
			}
		else
			{ prettyPrintIndent(indent+1); printf("(None ?)\n"); }

		if(cur->next)
			{
			if((cur->next->id==E_DECL_CONST)||(cur->next->id==E_DECL_VAR))
				{ prettyPrint(cur->next,indent+1); }	//next decl
			else
				{
				valueLeaf	*tmp=cur->next;

				prettyPrintIndent(indent+1); printf("(PREAST_NO_DECL\n");

				prettyPrintIndent(indent+2); printf("[\n");
				while(tmp)
					{
					prettyPrint(tmp,indent+3);

					if(tmp->next)
						{ prettyPrintIndent(indent+3); printf(";\n"); }

					tmp=tmp->next;
					}
				prettyPrintIndent(indent+2); printf("]\n");

				prettyPrintIndent(indent+1); printf(")\n");
				}
			}
		else
			{ prettyPrintIndent(indent+1); printf("(PREAST_NO_DECL [])\n"); }
		

		prettyPrintIndent(indent); printf(")\n");
		}

	/* ** statement ** */
	else if(cur->id==E_STM_ASG)
		{
		prettyPrintIndent(indent); printf("(PREAST_STM_ASG\n");
		prettyPrint(cur->param1,indent+1);
		prettyPrint(cur->param2,indent+1);
		prettyPrintIndent(indent); printf(")\n");
		}
	else if(cur->id==E_STM_WHILE)
		{
		prettyPrintIndent(indent); printf("(PREAST_STM_WHILE\n");
		prettyPrint(cur->param1,indent+1);
		prettyPrintBody(cur->param2,indent+1);
		prettyPrintIndent(indent); printf(")\n");
		}
	else if(cur->id==E_STM_IF)
		{
		valueLeaf	*tmp=cur->param1;

		prettyPrintIndent(indent); printf("(PREAST_STM_IF\n");

		prettyPrintIndent(indent+1); printf("(\\laquo\n");
		if(!tmp->next)
			{ prettyPrintIndent(indent+2); printf("£\n"); }
		while(tmp)
			{
			prettyPrintIndent(indent+2); printf("(pair ??\n");
			prettyPrint(tmp->param1,indent+3);
			prettyPrintBody(tmp->param2,indent+3);
			prettyPrintIndent(indent+2); printf(")\n");

			if(tmp->next)
				{
				if(tmp->next->next)
					{ prettyPrintIndent(indent+2); printf(";\n"); }
				else
					{ prettyPrintIndent(indent+2); printf("£\n"); }
				}

			tmp=tmp->next;
			}
		prettyPrintIndent(indent+1); printf("\\raquo)\n");

		// equivalenza: Some ? (PREAST_NO_DECL []) = None ?
		if(cur->param2)
			{
			prettyPrintIndent(indent+1); printf("(Some ?\n");
			prettyPrintBody(cur->param2,indent+2);	//body
			prettyPrintIndent(indent+1); printf(")\n");
			}
		else
			{ prettyPrintIndent(indent+1); printf("(None ?)\n"); }

		prettyPrintIndent(indent); printf(")\n");
		}
}

/* *************************** cPrint ***************************** */

void cPrintIndent(int indent)
{
	int	index;

	for(index=0;index<indent;index++)
		{ printf("\t"); }
}

void cPrintTypesAux(valueLeaf *type,int field)
{
	if(type->id==E_TYPE_STRUCT)
		{ printf("\tuser%d_t\tfield%d;\n\n",getUserType(type,NULL),field); }
	else if(type->id==E_TYPE_ARRAY)
		{
		char		bufferDim[256];
		valueLeaf	*tmp=type;

		memset(bufferDim,0,256);

		while(tmp->id==E_TYPE_ARRAY)
			{
			sprintf(&bufferDim[strlen(bufferDim)],"[%d]",tmp->param1->inumValue+1);
			tmp=tmp->param2;
			}

		if(tmp->id==E_TYPE_STRUCT)
			{ printf("\tuser%d_t\tfield%d%s;\n\n",getUserType(tmp,NULL),field,bufferDim); }
		else if(tmp->id==E_TYPE_DWORD)
			{ printf("\t_DWORD_\tfield%d%s;\n\n",field,bufferDim); }
		else if(tmp->id==E_TYPE_WORD)
			{ printf("\t_WORD_\tfield%d%s;\n\n",field,bufferDim); }
		else
			{ printf("\t_BYTE_\tfield%d%s;\n\n",field,bufferDim); }
		}
	else if(type->id==E_TYPE_DWORD)
		{ printf("\t_DWORD_\tfield%d;\n\n",field); }
	else if(type->id==E_TYPE_WORD)
		{ printf("\t_WORD_\tfield%d;\n\n",field); }
	else
		{ printf("\t_BYTE_\tfield%d;\n\n",field); }

	if(type->next)
		{ cPrintTypesAux(type->next,field+1); }
}

void cPrintTypes(void)
{
	int			index=1;
	valueLeaf	*cur=typeRoot;

	while(cur)
		{
		printf("typedef struct\n");
		printf("{\n");
		cPrintTypesAux(cur->param1,0);
		printf("} user%d_t;\n\n",index);

		cur=cur->next;
		index++;
		}
}

void cPrint(valueLeaf *cur,int indent)
{
	/* ** valori ** */
	if(cur->id==E_VALUE_INUM)
		{ printf("%lu",cur->inumValue); }
	else if(cur->id==E_VALUE_BYTE)
		{ printf("0x%02lX",(_DWORD_) cur->byteValue); }
	else if(cur->id==E_VALUE_WORD)
		{ printf("0x%04lX",(_DWORD_) cur->wordValue); }
	else if(cur->id==E_VALUE_DWORD)
		{ printf("0x%08lX",cur->dwordValue); }
	else if((cur->id==E_VALUE_ARRAY)||(cur->id==E_VALUE_STRUCT))
		{
		valueLeaf	*tmp=cur->param1;

		printf("{ ");
		while(tmp)
			{
			cPrint(tmp,indent);
			tmp=tmp->next;
			if(tmp)
				{ printf(", "); }
			}
		printf(" }");
		}

	/* ** variabili ** */
	else if((cur->id==E_VAR_ROOT)||(cur->id==E_VAR_STRUCT)||(cur->id==E_VAR_ARRAY))
		{
		valueLeaf	*tmp=cur;

		while(tmp->id!=E_VAR_ROOT)
			{
			tmp->next->last=tmp;
			tmp=tmp->next;
			}

		while(1)
			{
			if(tmp->id==E_VAR_ROOT)
				{ printf("%s",tmp->param1->stringValue); }
			else if(tmp->id==E_VAR_STRUCT)
				{ printf(".field%lu",tmp->param1->inumValue); }
			else if(tmp->id==E_VAR_ARRAY)
				{ printf("["); cPrint(tmp->param1,indent); printf("]"); }

			if(tmp==cur)
				{ break; }
			else
				{ tmp=tmp->last; }
			}
		}

	/* ** espressioni ** */
	else if(cur->id==E_EXPR_VAR)
		{ cPrint(cur->param1,indent); }
	else if(cur->id==E_EXPR_NOT)
		{ printf("!("); cPrint(cur->param1,indent); printf(")"); }
	else if(cur->id==E_EXPR_COM)
		{ printf("~("); cPrint(cur->param1,indent); printf(")"); }
	else if(cur->id==E_EXPR_NEG)
		{ printf("-("); cPrint(cur->param1,indent); printf(")"); }
	else if((cur->id==E_EXPR_W2B)||(cur->id==E_EXPR_DW2B))
		{ printf("((_BYTE_) ("); cPrint(cur->param1,indent); printf("))"); }
	else if((cur->id==E_EXPR_B2W)||(cur->id==E_EXPR_DW2W))
		{ printf("((_WORD_) ("); cPrint(cur->param1,indent); printf("))"); }
	else if((cur->id==E_EXPR_B2DW)||(cur->id==E_EXPR_W2DW))
		{ printf("((_DWORD_) ("); cPrint(cur->param1,indent); printf("))"); }
	else if(cur->id==E_EXPR_ADD)
		{ printf("("); cPrint(cur->param1,indent); printf(") + ("); cPrint(cur->param2,indent); printf(")"); }
	else if(cur->id==E_EXPR_SUB)
		{ printf("("); cPrint(cur->param1,indent); printf(") - ("); cPrint(cur->param2,indent); printf(")"); }
	else if(cur->id==E_EXPR_MUL)
		{ printf("("); cPrint(cur->param1,indent); printf(") * ("); cPrint(cur->param2,indent); printf(")"); }
	else if(cur->id==E_EXPR_DIV)
		{ printf("("); cPrint(cur->param1,indent); printf(") / ("); cPrint(cur->param2,indent); printf(")"); }
	else if(cur->id==E_EXPR_SHL)
		{ printf("("); cPrint(cur->param1,indent); printf(") << ("); cPrint(cur->param2,indent); printf(")"); }
	else if(cur->id==E_EXPR_SHR)
		{ printf("("); cPrint(cur->param1,indent); printf(") >> ("); cPrint(cur->param2,indent); printf(")"); }
	else if(cur->id==E_EXPR_AND)
		{ printf("("); cPrint(cur->param1,indent); printf(") & ("); cPrint(cur->param2,indent); printf(")"); }
	else if(cur->id==E_EXPR_OR)
		{ printf("("); cPrint(cur->param1,indent); printf(") | ("); cPrint(cur->param2,indent); printf(")"); }
	else if(cur->id==E_EXPR_XOR)
		{ printf("("); cPrint(cur->param1,indent); printf(") ^ ("); cPrint(cur->param2,indent); printf(")"); }
	else if(cur->id==E_EXPR_LT)
		{ printf("("); cPrint(cur->param1,indent); printf(") < ("); cPrint(cur->param2,indent); printf(")"); }
	else if(cur->id==E_EXPR_LTE)
		{ printf("("); cPrint(cur->param1,indent); printf(") <= ("); cPrint(cur->param2,indent); printf(")"); }
	else if(cur->id==E_EXPR_GT)
		{ printf("("); cPrint(cur->param1,indent); printf(") > ("); cPrint(cur->param2,indent); printf(")"); }
	else if(cur->id==E_EXPR_GTE)
		{ printf("("); cPrint(cur->param1,indent); printf(") >= ("); cPrint(cur->param2,indent); printf(")"); }
	else if(cur->id==E_EXPR_EQ)
		{ printf("("); cPrint(cur->param1,indent); printf(") == ("); cPrint(cur->param2,indent); printf(")"); }
	else if(cur->id==E_EXPR_NEQ)
		{ printf("("); cPrint(cur->param1,indent); printf(") != ("); cPrint(cur->param2,indent); printf(")"); }

	/* ** statement ** */
	else if(cur->id==E_STM_ASG)
		{
		cPrintIndent(indent); cPrint(cur->param1,indent); printf(" = "); cPrint(cur->param2,indent); printf(";\n\n");

		if(cur->next)
			{ cPrint(cur->next,indent); }
		}
	else if(cur->id==E_STM_WHILE)
		{
		cPrintIndent(indent); printf("while("); cPrint(cur->param1,indent); printf(")\n");
		cPrintIndent(indent+1); printf("{\n");
		cPrint(cur->param2,indent+1);
		cPrintIndent(indent+1); printf("}\n\n");

		if(cur->next)
			{ cPrint(cur->next,indent); }
		}
	else if(cur->id==E_STM_IF)
		{
		valueLeaf	*tmp=cur->param1;

		while(tmp)
			{
			cPrintIndent(indent); printf("%s(",(tmp==cur->param1) ? "if" : "else if"); cPrint(tmp->param1,indent); printf(")\n");
			cPrintIndent(indent+1); printf("{\n");
			cPrint(tmp->param2,indent+1);
			cPrintIndent(indent+1); printf("}\n");

			tmp=tmp->next;
			}

		if(cur->param2)
			{
			cPrintIndent(indent); printf("else\n");
			cPrintIndent(indent+1); printf("{\n");
			cPrint(cur->param2,indent+1);
			cPrintIndent(indent+1); printf("}\n");
			}

		printf("\n");

		if(cur->next)
			{ cPrint(cur->next,indent); }
		}

	/* ** dichiarazioni ** */
	else if((cur->id==E_DECL_CONST)||(cur->id==E_DECL_VAR))
		{
		valueLeaf	*tmp=cur->param1;
		char		bufferDim[256];

		memset(bufferDim,0,256);

		while(tmp->id==E_TYPE_ARRAY)
			{
			sprintf(&bufferDim[strlen(bufferDim)],"[%d]",tmp->param1->inumValue+1);
			tmp=tmp->param2;
			}

		cPrintIndent(indent);
		if(cur->id==E_DECL_CONST)
			{ printf("const "); }

		if(tmp->id==E_TYPE_STRUCT)
			{ printf("user%d_t\t",getUserType(tmp,NULL)); }
		else if(tmp->id==E_TYPE_DWORD)
			{ printf("_DWORD_\t"); }
		else if(tmp->id==E_TYPE_WORD)
			{ printf("_WORD_\t"); }
		else
			{ printf("_BYTE_\t"); }

		printf("%s%s",cur->param2->stringValue,bufferDim);

		if(cur->param3)
			{ printf(" = "); cPrint(cur->param3,indent); }
		printf(";\n\n");

		if(cur->next)
			{ cPrint(cur->next,indent); }
		}
}

/* *************************** main ******************************* */

int main(int argc,char **argv)
{
	int		ret;

	/* ignora eventuali errori di parametri */
	if(argc>1)
		{ usage(argv[0]); }

	ret=yyparse(NULL);

	if((!ret)&&(!numErr))
		{
		printf("(* matita language *)\n\n");
		printf("definition parsingResult \\def\n");
		printf(" (PREAST_ROOT\n");
		prettyPrint(&root,2);
		printf(" ).\n\n");

		printf("(* C language\n\n");
		printf("#ifndef\t__STDC__\n");
		printf("typedef\tunsigned __int32\t_DWORD_;\n");
		printf("typedef\tunsigned __int16\t_WORD_;\n");
		printf("typedef\tunsigned __int8\t_BYTE_;\n");
		printf("#else\n");
		printf("typedef\t__uint32_t\t_DWORD_;\n");
		printf("typedef\t__uint16_t\t_WORD_;\n");
		printf("typedef\t__uint8_t\t_BYTE_;\n");
		printf("#endif\n\n");
		cPrintTypes();
		printf("void main(void)\n");
		printf("{\n");
		cPrint(&root,1);
		printf("\treturn;\n\n");
		printf("}\n\n");
		printf("*)");
		}

	return(ret);
}
