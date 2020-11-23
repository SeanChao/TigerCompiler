# Yet Another Tiger Compiler

## Lex

### Handling Comments

By default, the lex is in `DEFAULT` state. It uses a global variable `com_cnt` to store the number of nested comments.
After match the beginning of a comment `/*`, it transfers to `COMMENT` state and add 1 to `com_cnt`.
In `COMMENT` state, it matches all characters that can appear in a comment.
If it matches `/*` then `com_cnt++` and continues mathching.
If it matches `*/` then decrements `com_cnt` and check whether `com_cnt == 0`. If so, then it transfers to `DEFAULT` state and ends the matching process of comments.

### Handling Strings

In `DEFAULT` state, if the lex matches `"` then it transfers to `STR` state, to match the whole string. Meanwhile, `adjust` is called and the `EM_tokPos` is recorded.
In `STR` state, my lex uses multiple rules to match the string literal. None of them update `EM_tokPos` in the process. The lex uses a global variable `sbuf` as a buffer to store patially matched string literals.
Matching normal characters like alphabet and numbers or other symbols is trivial. The lex just appends them to `sbuf`. If there are any escape sequences, the string is passed to `getstr` to translate its meaning.
Multiline strings `\f___f\` are ignored.
After match the `"` marking the end of string, the string is returned and `sbuf` is reset.

### Handling Errors

In `DEFAULT` state, if none of rules can match a word, then an error is reported by calling `EM_error`.

### Handling EOF

If lex reached `EOF`, `yyterminate` is called.

## Parser

### Shift/Reduce Conflicts

Two shift/reduce (S/R) conflicts lies in this grammar:

```bison
tydecs: tydec       {$$=A_NametyList($1, NULL);}
    | tydec tydecs  {$$=A_NametyList($1, $2);}

fundecs: fundec         {$$=A_FundecList($1, NULL);}
    | fundec fundecs    {$$=A_FundecList($1, $2);}
```

The S/R conflict does not matter because a shift followed by a reduce is essentially the same as a direct reduce.
