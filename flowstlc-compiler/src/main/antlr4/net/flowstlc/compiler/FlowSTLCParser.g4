parser grammar FlowSTLCParser;

options {
    tokenVocab = FlowSTLCLexer;
}

program : declarations EOF;

declarations : declaration*;

declaration
    : function_declaration
    | constant_declaration
    ;

constant_declaration :
    KW_VAL Identifier COLON type ASSIGN expr
;

function_declaration :
    function_type_declaration function_body_declaration;

function_type_declaration :
    KW_FUN Identifier COLON type;

function_body_declaration :
    KW_FUN Identifier function_argument_list? ASSIGN expr
;

function_argument_list :
    Identifier+
;

security_level
    : KW_SECRET #LevelSecret
    | KW_PUBLIC #LevelPublic
;

type
    : builtin_type                          #BuiltinType
    | type LBRACK security_level RBRACK     #ModalityType
    | type CARET security_level ARROW type  #FunctionType
;

builtin_type
    : KW_INT    #IntType
    | KW_UNIT   #UnitType
    | KW_BOOL   #BoolType
;

expr
    : simple_expression                                                                 #SimpleExpression
    | KW_LET Identifier ASSIGN LBRACK simple_expression RBRACK KW_IN simple_expression  #LetExpression
    | Identifier simple_expression+                                                     #FunctionCall
    | KW_IF simple_expression KW_THEN simple_expression KW_ELSE simple_expression       #IfExpression
;

simple_expression
    : literal                                                                           #LiteralExpression
    | LPAREN expr RPAREN                                                                #ParenthesizedExpression
    | Identifier                                                                        #IdentifierExpression
    // Multiplicative operators (highest precedence)
    | simple_expression MUL simple_expression                                           #MulExpression
    | simple_expression DIV simple_expression                                           #DivExpression
    | simple_expression MOD simple_expression                                           #ModExpression
    // Additive operators
    | simple_expression ADD simple_expression                                           #AddExpression
    | simple_expression SUB simple_expression                                           #SubExpression
    // Comparison operators
    | simple_expression LT simple_expression                                            #LessThanExpression
    | simple_expression LE simple_expression                                            #LessThanOrEqualExpression
    | simple_expression GT simple_expression                                            #GreaterThanExpression
    | simple_expression GE simple_expression                                            #GreaterThanOrEqualExpression
    | simple_expression EQUAL simple_expression                                         #EqualExpression
    | simple_expression NOTEQUAL simple_expression                                      #NotEqualExpression
    // Logical operators (lowest precedence)
    | simple_expression KW_AND simple_expression                                        #AndExpression
    | simple_expression KW_OR simple_expression                                         #OrExpression
    | KW_NOT simple_expression                                                          #NotExpression
    | SUB simple_expression                                                             #NegateExpression
    | LBRACK simple_expression RBRACK                                                   #ModalityExpression
;

literal
    : IntegerLiteral    #IntLiteral
    | BooleanLiteral    #BoolLiteral
    | KW_UNIT_LITERAL   #UnitLiteral
;