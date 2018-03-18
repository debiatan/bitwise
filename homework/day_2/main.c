#include <stdio.h>
#include <string.h>
#include <stddef.h>
#include <stdint.h>

#include <assert.h>
#include "stretchy.c"

void *xcalloc(size_t num_bytes) {
    void *ptr = calloc(1, num_bytes);
    if (!ptr) {
        perror("xcalloc failed");
        exit(1);
    }
    return ptr;
}

#define BP __builtin_debugtrap();
#define NotImplemented __builtin_debugtrap();
#define ARRAY_LEN(x) ((int)(sizeof(x)/sizeof(*(x))))
typedef uint32_t U32;
typedef uint64_t U64;
typedef uint32_t B32;
typedef uint8_t Byte;

typedef enum{
    ParserState_ExpectingSubExpression,
    ParserState_Complete,
    ParserState_Complete_Reject_Symbol_Extension,
    ParserState_Error
} ParserState;

typedef enum{
    Arity_Leaf,
    Arity_Unary,
    Arity_Binary,
} Arity;
typedef enum{
    Associativity_Null,
    Associativity_Left,
    Associativity_Right,
} Associativity;
typedef struct Operator{
    char c;
    U32 precedence;
    Arity arity;
    Associativity associativity;
    U32 neutral_element;
} Operator;

typedef struct expr_t Expr;
struct expr_t{
    Arity arity;

    Expr *parent;

    union{
        struct{
            B32 initialized;
            U64 literal_value;
        };
        struct{
            Operator *op;
            union{
                struct{             // NOTE: ExprKind_Unary
                    Expr *unary;
                };
                struct{             // NOTE: ExprKind_Binary
                    Expr *left;
                    Expr *right;
                };
                Expr *elements[2];
            };
        };
    };

    U32 parens_level;
};

typedef struct Parser{
    ParserState state;
    Operator *operator_buf;
    Expr sentinel;
    Expr *cur;
    U32 parens_level;
} Parser;

Operator * get_operator(Parser *parser, Arity arity, char c){
    Operator *result = 0;

    for(U32 i=0; i < buf_len(parser->operator_buf); ++i){
        Operator *op = parser->operator_buf+i;
        if(arity == op->arity && op->c == c){
            result = op;
            break;
        }
    }

    return result;
}

Expr * push_child_(Parser *parser, Expr *parent){
    Expr *result = (Expr *) xcalloc(sizeof(Expr));
    result->parent = parent;
    result->parens_level = parser->parens_level;
    return result;
}

#define push_child_under_role(parser, parent, role) push_child_offset_(parser, parent, offsetof(Expr, role))
Expr * push_child_offset_(Parser *parser, Expr *parent, U32 role_offset){
    Expr *result = push_child_(parser, parent);
    Expr **child_slot = (Expr **) ((Byte *)parent + role_offset);
    *child_slot = result;
    return result;
}

Parser * create_parser(){
    Parser *result = xcalloc(sizeof(Parser));
    result->cur = push_child_under_role(result, &result->sentinel, unary);
    buf_free(result->operator_buf);

    return result;
}

Expr * future_op_subtree(Parser *parser, Arity arity, Operator *op){
    Expr *result = parser->cur;
      {
        Expr *parent = result->parent;
        while(parent != &parser->sentinel){
            U32 parent_op_precedence = parent->op->precedence;

            // NOTE: This rule supports unary prefix and binary left-associative operators
            // B32 stop = parent_op_precedence < op->precedence;

            // NOTE: This rule supports unary prefix and binary left- and right-associative operators
            // if(parent->op->arity == Arity_Binary && parent->op->associativity == Associativity_Left){
            //     ++parent_op_precedence;
            // }
            // B32 stop = parent_op_precedence <= op->precedence;

            // NOTE: This rule supports unary prefix, binary left- and right-associative operators and parentheses
            if(parent->op->arity == Arity_Binary && parent->op->associativity == Associativity_Left){
                ++parent_op_precedence;
            }

            B32 stop = ((parent_op_precedence <= op->precedence || parent->parens_level != parser->parens_level) &&
                        result->parens_level == parser->parens_level);

            if(stop){
                break;
            }
            else{
                result = parent;
                parent = parent->parent;
            }
        }
      }

    return result;
}

Expr * alloc_displace(Parser *parser, Expr *target){
    Expr *result = push_child_(parser, target->parent);

    // NOTE: displace target child expression
    for(U32 i_subexpr = 0; i_subexpr < ARRAY_LEN(target->parent->elements); ++i_subexpr){
        if(target->parent->elements[i_subexpr] == target){
            target->parent->elements[i_subexpr] = result;
            break;
        }
    }

    return result;
}

void expand_number_literal(Parser *parser, char c){
    parser->cur->initialized = 1;
    parser->cur->literal_value *= 10;
    parser->cur->literal_value += c-'0';
}

void feed(Parser *parser, char c){
    Operator *op = 0;
    Expr *cur = parser->cur;
    switch(parser->state){
      case ParserState_ExpectingSubExpression:
          {
            if(c >= '0' && c <= '9'){
                cur->arity = Arity_Leaf;
                expand_number_literal(parser, c);
                parser->state = ParserState_Complete;
            }
            else if(c == ' '){
                // NOTE: ignore
            }
            else if(c == '('){
                ++cur->parens_level;
                ++parser->parens_level;
            }
            else if((op = get_operator(parser, Arity_Unary, c))){
                cur->arity = Arity_Unary;
                cur->op = op;
                cur = push_child_under_role(parser, cur, unary);
            }
            else{
                parser->state = ParserState_Error;
            }
          } break;
      case ParserState_Complete:
      case ParserState_Complete_Reject_Symbol_Extension:
          {
            if(c >= '0' && c <= '9' &&
               parser->state != ParserState_Complete_Reject_Symbol_Extension){
                assert(cur->arity == Arity_Leaf);
                expand_number_literal(parser, c);
            }
            else if(c == ' '){
                parser->state = ParserState_Complete_Reject_Symbol_Extension;
            }
            else if(c == ')'){
                if(!parser->parens_level){
                    parser->state = ParserState_Error;
                }
                else{
                    --parser->parens_level;
                    parser->state = ParserState_Complete_Reject_Symbol_Extension;
                }
            }
            else if((op = get_operator(parser, Arity_Binary, c))){
                Expr *future_left_subtree = future_op_subtree(parser, Arity_Binary, op);

                Expr *op_node = alloc_displace(parser, future_left_subtree);
                  {
                    op_node->arity = Arity_Binary;
                    op_node->op = op;
                    assert(!(op_node)->left);
                    op_node->left = future_left_subtree;
                  }

                future_left_subtree->parent = op_node;

                cur = push_child_under_role(parser, op_node, right);
                parser->state = ParserState_ExpectingSubExpression;
            }
            else{
                parser->state = ParserState_Error;
            }
          } break;
      case ParserState_Error:
          {
            // NOTE: No way out of here
          } break;
    }

    parser->cur = cur;
}

typedef struct StrBuf{
    char *s;
} StrBuf;
void push_str(StrBuf *buf, char *s){
    while(*s){
        buf_push(buf->s, *s++);
    }
}

void to_s_expression(Expr *expr, StrBuf *buf){
    switch(expr->arity){
      case Arity_Leaf:
          {
            U64 v = expr->literal_value;
            if(!expr->initialized){
                v = expr->parent->op->neutral_element;
            }
            char tmp[21];
            sprintf(tmp, "%lu", v);
            push_str(buf, tmp);
          } break;
      case Arity_Unary:
          {
            buf_push(buf->s, '(');
            buf_push(buf->s, expr->op->c);
            buf_push(buf->s, ' ');
            to_s_expression(expr->unary, buf);
            buf_push(buf->s, ')');
          } break;
      case Arity_Binary:
          {
            buf_push(buf->s, '(');
            buf_push(buf->s, expr->op->c);
            buf_push(buf->s, ' ');
            to_s_expression(expr->left, buf);
            buf_push(buf->s, ' ');
            to_s_expression(expr->right, buf);
            buf_push(buf->s, ')');
          } break;
      default: NotImplemented; break;
    }
}

typedef struct Test{
    Operator *operator_table;
    char *input;
    char *expected_output;
    char *comment;
} Test;

int main(void){
    Operator operator_table_homework_example[] = {
          { '~',  3, Arity_Unary,  Associativity_Right },
          { '*',  2, Arity_Binary, Associativity_Left  },
          { '/',  2, Arity_Binary, Associativity_Left  },
          { '+',  1, Arity_Binary, Associativity_Left  },
          { '-',  1, Arity_Binary, Associativity_Left  },
          {},
    };

    Operator operator_table_arithmetic[] = {
          { '^',  4, Arity_Binary, Associativity_Right, 1},
          { '-',  3, Arity_Unary,  Associativity_Right, 0},
          { '*',  2, Arity_Binary, Associativity_Left,  1},
          { '/',  2, Arity_Binary, Associativity_Left,  1},
          { '+',  1, Arity_Binary, Associativity_Left,  0},
          { '-',  1, Arity_Binary, Associativity_Left,  0},
          {},
    };

    Test test[] = {
          {
            .operator_table  =  operator_table_homework_example,
            .input           = "12*34 + 45/56 + ~25", 
            .expected_output = "(+ (+ (* 12 34) (/ 45 56)) (~ 25))",
            .comment         = "Homework example"
          },
          {
            .operator_table  =  operator_table_arithmetic,
            .input           = "1 + 2 * (3 - 4) - -5^6+7 + 8^(9/10)", 
            .expected_output = "(+ (+ (- (+ 1 (* 2 (- 3 4))) (- (^ 5 6))) 7) (^ 8 (/ 9 10)))",
            .comment         = "arithmetic example"
          },
    };

    for(U32 i_test = 0; i_test < ARRAY_LEN(test); ++i_test){
        Parser *parser = create_parser();
        for(Operator *op = test[i_test].operator_table; op->c; ++op){
            buf_push(parser->operator_buf, *op);
        }

        char *input = test[i_test].input;
        U32 input_len = strlen(input);

        printf("%s:\n", test[i_test].comment); for(U32 i=0; i<strlen(test[i_test].comment); ++i) printf("="); printf("\n");

        for(U32 i = 0; i < input_len; ++i){
            feed(parser, input[i]);

            if(input[i] != ' '){
                printf("%.*s%*s -> ", i+1, input, input_len-i-1, "");

                if(parser->state == ParserState_Error){
                    printf("Parsing error");
                    break;
                }
                else{
                    StrBuf buf = {};
                    to_s_expression(parser->sentinel.unary, &buf);
                    printf("%.*s\n", (U32)buf_len(buf.s), buf.s);
                }
            }
        }

        StrBuf buf = {};
        to_s_expression(parser->sentinel.unary, &buf);

        assert(parser->state == ParserState_Error || !strcmp(buf.s, test[i_test].expected_output));
        printf("\n");
    }

     
    return 0;
}
