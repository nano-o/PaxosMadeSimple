------------------------------ MODULE Library ------------------------------

EXTENDS Sequences, Naturals, FiniteSets

Last(s) == s[Len(s)]

Some(S) == CHOOSE e \in S : TRUE

Min(i,j) == IF i < j THEN i ELSE j
Max(S, LessEq(_,_)) == CHOOSE e \in S : \A e1 \in S : LessEq(e1,e)

Image(f) == {f[x] : x \in DOMAIN f}

\* Sequences with no duplicates:

RECURSIVE NoDupRec(_,_)
NoDupRec(es, seen) == 
    IF es = <<>> 
    THEN TRUE 
    ELSE
        IF es[1] \in seen 
        THEN FALSE 
        ELSE NoDupRec(Tail(es), seen \cup {es[1]})
NoDup(es) == 
  NoDupRec(es,{})
NoDupSeq(E) == 
  {es \in Seq(E) : NoDup(es)}

\* Removing duplicates from a sequence:

RECURSIVE RemDupRec(_,_)
RemDupRec(es, seen) ==
  IF es = <<>>
  THEN <<>>
  ELSE
    IF es[1] \in seen
    THEN RemDupRec(Tail(es), seen)
    ELSE <<es[1]>> \o RemDupRec(Tail(es), seen \cup {es[1]}) 
RemDup(es) == RemDupRec(es, {})

\* Sequence prefixes:

Prefix(s1,s2) == 
    /\  Len(s1) <= Len(s2)
    /\  \A i \in DOMAIN s1 : s1[i] = s2[i]

\* The longest common prefix of two sequences:

RECURSIVE LongestCommonPrefixLenRec(_,_,_)
LongestCommonPrefixLenRec(S,n,e1) ==
    IF S = {}
    THEN 0
    ELSE
        IF /\ \A e \in S : Len(e) >= n+1
           /\ \A e \in S : e[n+1] = e1[n+1]
        THEN LongestCommonPrefixLenRec(S,n+1,e1)
        ELSE n
    
LongestCommonPrefixLenSet(S) == LongestCommonPrefixLenRec(S, 0, Some(S))

LongestCommonPrefix(S) ==
    LET n == LongestCommonPrefixLenSet(S)
    IN  IF n = 0
        THEN <<>>
        ELSE [i \in 1..LongestCommonPrefixLenSet(S) |-> Some(S)[i]]

RECURSIVE TruncateRec(_,_,_)
TruncateRec(x,xs,n) ==
    IF xs[n] = x 
    THEN [i \in 1..n |-> xs[i]]
    ELSE TruncateRec(x,xs,n+1)
Truncate(x,xs) == TruncateRec(x,xs,1)
    
        
=============================================================================
\* Modification History
\* Last modified Fri May 22 18:55:17 CEST 2015 by glo
\* Last modified Thu May 21 16:34:03 CEST 2015 by glo
\* Last modified Wed Jan 29 17:03:15 CET 2014 by nano
\* Last modified Thu Dec 05 10:49:14 CET 2013 by losa
\* Created Mon Aug 05 15:49:10 CEST 2013 by losa
