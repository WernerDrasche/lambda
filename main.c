#define STB_DS_IMPLEMENTATION
#include <stdio.h>
#include <stb_ds.h>
#include <assert.h>
#include <err.h>
#include <stdbool.h>

enum token_t { LAMBDA, SYMBOL, DOT, LBRACKET, RBRACKET, SEMICOLON };

struct token {
    enum token_t t;
    union {
        unsigned symbol;
    };
};

char leading_ones(char byte) {
	char count;
	for (count = 0; count < 8; ++count) {
		if (!(byte & 0x80)) break;
		byte <<= 1;
	}
	return count;
}

struct token *tokenize(const char *str) {
    struct token *tokens = NULL;
    unsigned char c;
    struct token token;
    while ((c = *str)) {
        if (c <= ' ' || c == 127) {
			++str;
			continue;
		}
		bool symbol = false;
        switch (c) {
            case '@': token.t = LAMBDA; break;
            case '(': token.t = LBRACKET; break;
            case ')': token.t = RBRACKET; break;
            case '.': token.t = DOT; break;
            case ';': token.t = SEMICOLON; break;
            default: 
				token.t = SYMBOL; 
				char n = leading_ones(c);
				if (n == 0) {
					n = 1;
				}
				token.symbol = 0;
				for (char i = 0; i < n; ++i) {
					token.symbol >>= 8;
					token.symbol |= str[i] << 24;
				}
				token.symbol >>= (sizeof(token.symbol) - n) * 8;
				if (token.symbol == 0xbbce) {
					token.t = LAMBDA;
				}
				str += n - 1;
				break;
        }
        arrput(tokens, token);
		++str;
    }
    return tokens;
}

enum expression_t { VARIABLE, FUNCTION, APPLICATION };

struct expression {
    union {
        struct variable {
            unsigned id;
            unsigned depth;
        } v;
        struct function {
            struct function *parent;
            unsigned *params;
            unsigned n;
            unsigned i;
            unsigned *rc;
            struct expression *body;
        } f;
        struct application {
            struct expression *left;
            struct expression *right;
            bool enclosed;
        } a;
    };
    enum expression_t t;
    unsigned consumed;
};

struct macro {
    unsigned key;
    struct expression *value;
};

struct macro *macros = NULL;

struct expression *parse(struct token *tokens, unsigned n, struct function *f) {
    if (n == 0) return NULL;
    struct expression *expr;
    enum token_t t = tokens->t;
    if (t == LBRACKET) {
        unsigned depth = 1;
        unsigned i;
        for (i = 1; depth && i < n; ++i) {
            enum token_t t = tokens[i].t;
            switch (tokens[i].t) {
                case LBRACKET: ++depth; break;
                case RBRACKET: --depth; break;
                default: break;
            }
        }
        if (depth || n == 1) {
            errx(1, "unmatched (");
        }
        expr = parse(tokens + 1, i - 2, f);
        expr->consumed += 2;
        if (expr->t == APPLICATION) {
            expr->a.enclosed = true;
        }
        goto next;
    }
    if (t == RBRACKET) {
        errx(1, "unmatched )");
    }
    expr = malloc(sizeof(struct expression));
    if (t == SYMBOL) {
        unsigned symbol = tokens->symbol;
        struct function *cur;
        unsigned depth = 0;
        for (cur = f; cur; cur = cur->parent, ++depth) {
            unsigned *params = cur->params;
            unsigned num_params = cur->n;
            for (unsigned i = 0; i < num_params; ++i) {
                if (params[i] == symbol) {
                    ++depth;
                    goto found;
                }
            }
        }
        depth = 0;
found:
        *expr = (struct expression){
            .t = VARIABLE,
            .consumed = 1,
            .v = {.id = symbol, .depth = depth},
        };
        goto next;
    }
    if (t == LAMBDA) {
        unsigned i;
        unsigned *params = NULL;
        bool complete = false;
        for (i = 1; i < n; ++i) {
            struct token tok = tokens[i];
            enum token_t t = tok.t;
            if (t == SYMBOL) {
                arrput(params, tok.symbol);
            } else if (t == DOT) {
                complete = true;
                ++i;
                break;
            } else {
                errx(1, "parameter list has to consist of symbols only");
            }
        }
        if (!complete || i == 2) {
            errx(1, "incomplete lambda function (missing . or parameter)");
        }
        unsigned num_params = i - 2;
        unsigned *rc = malloc(sizeof(unsigned));
        *rc = 1;
        *expr = (struct expression){
            .t = FUNCTION,
            .f = {.parent = f, .params = params, .n = num_params, .rc = rc},
        };
        struct expression *body = parse(tokens + i, n - i, &expr->f);
        if (body == NULL) {
            errx(1, "lambda body mustn't be empty");
        }
        expr->f.body = body;
        expr->consumed = 2 + num_params + body->consumed;
        goto next;
    }
    errx(1, "encountered . outside of function declaration");
    
    unsigned consumed;
    struct expression *right;
next:
    consumed = expr->consumed;
    right = parse(tokens + consumed, n - consumed, f);
    if (!right) return expr;
    struct expression *app = malloc(sizeof(struct expression));
    *app = (struct expression){
        .t = APPLICATION,
        .consumed = consumed + right->consumed,
        .a = {.left = expr, .right = right},
    };
    return app;
}

struct expression *fix_associativity(struct expression *expr) {
    struct expression *left, *right;
    switch (expr->t) {
        case APPLICATION:
            left = expr->a.left;
            right = fix_associativity(expr->a.right);
            if (right->t == APPLICATION && !right->a.enclosed) {
                struct expression *x, *y, *z;
                x = left;
                y = right->a.left;
                z = right->a.right;
                expr->a.left = right;
                left = right;
                left->a.left = x;
                left->a.right = y;
                expr->a.right = z;
            }
            expr->a.left = fix_associativity(expr->a.left);
            break;
        case FUNCTION:
            expr->f.body = fix_associativity(expr->f.body);
            break;
        case VARIABLE:
            break;
    }
    return expr;
}

struct expression *copy(struct expression *expr) {
    struct expression *res = malloc(sizeof(struct expression));
    memcpy(res, expr, sizeof(struct expression));
    switch (expr->t) {
        case APPLICATION:
            res->a.left = copy(expr->a.left);
            res->a.right = copy(expr->a.right);
            break;
        case FUNCTION:
            res->f.parent = NULL; //only needed that for parsing
            res->f.body = copy(expr->f.body);
            *res->f.rc += 1;
            break;
        case VARIABLE:
            break;
    }
    return res;
}

void adjust_depth(struct expression *expr, int amount, unsigned depth) {
    switch (expr->t) {
        case VARIABLE:
            if (expr->v.depth > depth) {
                expr->v.depth += amount;
            }
            break;
        case FUNCTION:
            adjust_depth(expr->f.body, amount, depth + 1);
            break;
        case APPLICATION:
            adjust_depth(expr->a.left, amount, depth);
            adjust_depth(expr->a.right, amount, depth);
            break;
    }
}

struct expression *replace(
        struct expression *dest,
        unsigned id, unsigned depth,
        struct expression *src) 
{
    if (dest->t == VARIABLE && dest->v.id == id && dest->v.depth == depth) {
        free(dest);
        struct expression *expr = copy(src);
        adjust_depth(expr, depth, 0);
        return expr;
    }
    if (dest->t == FUNCTION) {
        dest->f.body = replace(dest->f.body, id, depth + 1, src);
    } else if (dest->t == APPLICATION) {
        dest->a.left = replace(dest->a.left, id, depth, src);
        dest->a.right = replace(dest->a.right, id, depth, src);
    }
    return dest;
}

///not recursive
void free_function(struct function *f) {
    unsigned rc = --*f->rc;
    if (rc == 0) {
        arrfree(f->params);
		free(f->rc);
    }
    free(f);
}

void free_all(struct expression *expr) {
    switch (expr->t) {
        case VARIABLE:
            free(expr);
            break;
        case APPLICATION:
            free_all(expr->a.left);
            free_all(expr->a.right);
            free(expr);
            break;
        case FUNCTION:
            free_all(expr->f.body);
            free_function((struct function *)expr);
            break;
    }
}

///assumes little endian
void print(struct expression *expr) {
    if (!expr) return;
	char buf[sizeof(unsigned) + 1] = {0};
    switch (expr->t) {
        case VARIABLE:
			*(unsigned *)buf = expr->v.id;
            printf("%s", buf);
            break;
        case APPLICATION:
            putc('(', stdout);
            print(expr->a.left);
            putc(' ', stdout);
            print(expr->a.right);
            putc(')', stdout);
            break;
        case FUNCTION:
			printf("λ");
            unsigned *params = expr->f.params;
            for (unsigned i = expr->f.i; i < expr->f.n; ++i) {
                memcpy(buf, params + i, sizeof(unsigned));
                printf("%s", buf);
            }
            putc('.', stdout);
            print(expr->f.body);
            break;
    }
}

struct expression *apply(struct application *app);
struct expression *apply_all(struct expression *expr) {
    switch (expr->t) {
        case APPLICATION:
            return apply((struct application *)expr);
        case FUNCTION:
            expr->f.body = apply_all(expr->f.body);
            break;
        case VARIABLE:
            break;
    }
    return expr;
}

struct expression *apply(struct application *app) {
    struct expression *left = app->left = apply_all(app->left);
    unsigned midx;
    if (left->t == VARIABLE && left->v.depth == 0 && (midx = hmgeti(macros, left->v.id)) != -1) {
        free(app->left);
        left = app->left = apply_all(copy(macros[midx].value));
    }
    struct expression *right = app->right = apply_all(app->right);
    if (left->t == FUNCTION) {
        bool enclosed = app->enclosed;
        free(app);
        unsigned i = left->f.i++;
        unsigned id = left->f.params[i];
        struct expression *body = left->f.body;
        body = replace(body, id, 1, right);
        free_all(right);
        //body = fix_associativity(body);
        //print(body);
        //putc('\n', stdout);
        body = apply_all(body);
        if (i == left->f.n - 1) {
            free_function(&left->f);
            adjust_depth(body, -1, 1);
            if (body->t == APPLICATION) {
                body->a.enclosed = enclosed;
            }
            return body;
        }
        left->f.body = body;
        return left;
    }
    return (struct expression *)app;
}

void load_macros_from_file(const char *filepath) {
    FILE *f = fopen(filepath, "r");
    if (!f) {
        err(1, "open failed (%s)", filepath);
    }
    if (fseek(f, 0, SEEK_END)) {
        err(1, "seek to end failed (%s)", filepath);
    }
    long size = ftell(f);
    if (size == -1) {
        err(1, "ftell failed (%s)", filepath);
    }
    rewind(f);
    char *buf = malloc(size + 1);
    size_t num_read = fread(buf, 1, size, f);
    if (num_read != size) {
        err(1, "read failed (%s)", filepath);
    }
	fclose(f);
    buf[size] = 0;
    struct token *tokens = tokenize(buf);
    unsigned n = arrlen(tokens);
    struct token *start = tokens;
    struct token *end = start + n;
    while (start != end) {
        if (start->t != SYMBOL) {
            errx(1, "macro declaration must start with symbol as identifier");
        }
        unsigned id = start->symbol;
        ++start;
		if (start->t != SYMBOL || start->symbol != '=') {
            errx(1, "= must follow after macro identifier");
        }
        ++start;
        unsigned i;
        for (i = 0; start + i != end && start[i].t != SEMICOLON; ++i);
        if (i == 0) {
            errx(1, "macro expression can't be empty");
        }
        if (start + i == end) {
            errx(1, "macro definition must end with ;");
        }
        struct expression *expr = parse(start, i, NULL);
        expr = fix_associativity(expr);
        if (expr->t == APPLICATION) {
            expr->a.enclosed = true;
        }
        hmput(macros, id, expr);
        start += i + 1;
    }
    arrfree(tokens);
    free(buf);
}

void eval(const char *prog) {
    struct token *tokens = tokenize(prog);
    unsigned n = arrlen(tokens);
    struct expression *expr = fix_associativity(parse(tokens, n, NULL));
    print(expr);
    putc('\n', stdout);
    expr = apply_all(expr);
    print(expr);
    puts("\n");
    free_all(expr);
    arrfree(tokens);
}

void free_macros(void) {
	unsigned n = hmlen(macros);
    for (unsigned i = 0; i < n; ++i) {
		free_all(macros[i].value);
	}
	hmfree(macros);
}

//for debug purposes
void print_macros(void) {
    unsigned n = hmlen(macros);
    for (unsigned i = 0; i < n; ++i) {
        struct macro *m = macros + i;
        putc(m->key, stdout);
        printf(" = ");
        print(m->value);
        putc('\n', stdout);
    }
}

int test(void) {
	eval("@x.x");
	return 0;
}

int main(void) {
    load_macros_from_file("macros.lmd");
    //eval("(@x.x)x");
    //eval("(@a.(@x.ax)b)@x.xaxa");
    //eval("((@bs.(@xa.(@ya.x)x)(@h.s))b)z");
    //eval("(@wyx.y(wyx))(@sz.s(s(s(z))))");
    //eval("(@sz.s(sz))(@wyx.y(wyx))(@uv.u(u(uv)))");
    //eval("(@uv.u(u(uv)))(@wyx.y(wyx))((@sz.s(s(s(s(sz)))))(@wyx.y(wyx))(@uv.u(u(uv))))");
    //eval("(@xyz.x(yz))(@uv.u(u(u(uv))))(@uv.u(u(uv)))");
    //eval("(@x.(b (x a))(b (x c)))(@a.a)");
    eval("λx.∨(Z1)(Z0)");
	free_macros();
    return 0;
}
