# Yet Another Tiger Compiler

## Parser

### Shift/Reduce Conflicts

Two shift/reduce (S/R) conflicts lies in this grammar:

```bison
tydecs: tydec       {$$=A_NametyList($1, NULL);}
    | tydec tydecs  {$$=A_NametyList($1, $2);}

fundecs: fundec         {$$=A_FundecList($1, NULL);}
    | fundec fundecs    {$$=A_FundecList($1, $2);}
```

I'm forced to use a right recursion grammar due to the restrictions of provided constructors. The S/R conflict does not matter because a shift followed by a reduce is essentially the same as a direct reduce.
