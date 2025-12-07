---
title: ALG Problem Set 2
header-includes: |
  \usepackage{algorithm}
  \usepackage[noend]{algpseudocode}
  \usepackage{float}
  \usepackage{caption}
  \usepackage{forest}
  \usepackage{tikz}
  \usetikzlibrary{arrows.meta, decorations.pathreplacing}
  \algrenewcommand\algorithmiccomment[1]{\hfill// #1}
---
## Problem 1
To design an algorithm which takes an infix expression and outputs the corresponding postfix expression. The first
attempt may use divide-and-conquer method: finds the main operator (the operator that will be executed last) and recursively solves the left and right sub-expressions. If we brute force to find the main operator, the running time will be $O(n^2)$ in the worst case. We can optimize it to $O(n)$ by adding a operator specifier in each recursive call. The idea is: if the main operator is $+$, then in the right sub-expression, there is no more $+$ operator, and the scanner can stop when it meets a $\times$.

\begin{algorithm}[H]
// The initial call is InfixToPostfix($A, 1, n, +$).
\caption*{InfixToPostfix($A, l, r, op$)}
\begin{algorithmic}[1]
    \State $NEXT=\{+:\times, \times:\ !, \ !:\text{null}\}$
    \If{$l > r$}
        \State \Return
    \EndIf
    \If{$l=r$}
        \State output $A[l]$
        \State \Return
    \EndIf
    \For{$i = r$ downto $l$}
        \If{$A[i] = op$}
            \State $\text{InfixToPostfix}(A, l, i - 1, op)$
            \State $\text{InfixToPostfix}(A, i + 1, r, NEXT[op])$
            \State output $A[i]$
            \State \Return
        \EndIf
    \EndFor
    \State $\text{InfixToPostfix}(A, l, r, NEXT[op])$
\end{algorithmic}
\end{algorithm}

Analysis of running time:

Each character is scanned at most $f(op)$ times, where $f(+)=3, f(\times)=2, f(!)=1$:
\begin{description}
\item[Base case:] $l=r$, the character is scanned once.
\item[Induction:] $l<r$, if the main operator is found at position $k$, the left sub-array $A[l, k-1]$ is only scanned in line 9 at most $f(op)$ times by induction hypothesis. And the right sub-expression $A[k+1, r]$ is scanned at most $f(NEXT[op])=f(op)-1$ times in recursion, plus 1 scan in the current call.
If the main operator is not found, the whole expression is scanned once, and then the sub-expression is scanned at most $f(NEXT[op])$ times by induction hypothesis. So the total times is at most $1+f(NEXT[op])=f(op)$.
\end{description}
So the total running time is $O(n)$.

## Problem 2
\begin{description}
\item[(a)] We guess that $\forall n\ge n_0, T(n)\ge cn$ for some constant $c>0$. The base case is $T(n_0)=2\ge cn_0$, so long as $c\le 2/n_0$. For the induction step, we have:
$T(n)\ge c\cdot\frac{n}{4}+c\cdot\frac{3n}{4}=cn$. The inequality $T(n)\ge cn$ always holds. We can let $c=2/n_0$ and the induction gives $\forall n\ge n_0, T(n)\ge cn$. So $T(n)=\Omega(n)$.
\renewcommand{\a}{\alpha}
\item[(b)] Without loss of generality, assume $1/2\le\a<1$, we can draw the recursion tree for $T(n)=T(\a n)+T((1-\a)n)+\Theta(n)$
(the asymptotic constant $c$ is omitted) as follows:

\forestset{
    sd/.style={
        edge={dash pattern=on 1.5pt off 2.5pt},
    }
}
\begin{forest}
for tree={math content, s sep=0.4cm},
tikz={
    \coordinate (left_x) at ([xshift=-0.6cm]bottom_left.west);
    \draw[{Stealth}-{Stealth}] (left_x |- level0.north) -- (left_x |- bottom_left.south) node[midway, left]
    {$\log_{\a}n$};
    \coordinate (right_x) at ([xshift=1.2cm]bottom_right.east);
    \draw[{Stealth}-{Stealth}] (right_x |- level0.north) -- (right_x |- bottom_right.south) node[midway, right]
    {$\log_{1-\a} n$};
    \foreach \i in {0,1,2}{
        \draw[-{Latex}, dotted] ([xshift=0.1cm]level\i.east) -- ([xshift=-0.5cm]level\i -| right_x) node[right] {$n$};
    }
},
[n, name=level0
    [\a n
        [\a^2 n [[1, sd, name=bottom_left]] [[1, sd]]]
        [\a(1-\a)n [[1, l=0, sd]] [[\cdots, no edge, l=0]]]
    ]
    [(1-\a)n, name=level1
        [\a(1-\a)n [\cdots, sd, l=1.2cm, inner sep=6pt] [1, sd, l=1.2cm]]
        [(1-\a)^2 n, name=level2 [1, sd] [1, sd, name=bottom_right]]
    ]
]
\end{forest}

Note that if $\a\neq 1/2$, the tree is unbalanced.
Assume $T(n)=T(\a n)+T((1-\a)n)+f(n)$, and $c_1n\le f(n)\le c_2 n$ for some constants $c_1, c_2>0$ and sufficiently large $n$.
For the top $\log_{1-\a} n$ levels, it is a full binary tree, and the total cost of each level $\ge c_1n$. Hence
the total cost of the top $\log_{1-\a} n$ levels $\ge c_1n\log_{1-\a} n$. $T(n)\ge c_1n\log_{1-\a} n=\Omega(n\log n)$.

If we extend the tree to the bottom, the total number of levels is $\log_{\a} n$. The total cost of each level $\le c_2 n$. Hence the total cost of the whole tree $\le c_2 n\log_{\a} n$. So $T(n)\le c_2 n\log_{\a} n=O(n\log n)$.

As a result, $T(n)=\Theta(n\log n)$.
\end{description}

## Problem 3
\begin{description}
\item[(a)] $S(m)=T(2^m)=2T(2^{m/2})+\Theta(m)=2S(m/2)+\Theta(m)$
\item[(b)] By Master Theorem, $S(m)=\Theta(m\log m)$. So $T(n)=S(\log n)=\Theta(\log n\log \log n)$.
\item[(c)] Let $m=\log_3 n$ and $R(m)=T(3^m)$, then $R(m)=T(3^m)=3T(3^{m/3})+\Theta(3^m)=3R(m/3)+\Theta(3^m)$.
$R(m)$ fits the standard form of Master Theorem: $R(m)=aR(m/b)+f(m)$, where
$a=3, b=3, f(m)=3^m$. Since $f(m)=\Omega(m^{\log_3(3)+\epsilon})$ and $3f(m/3)=3^{m/3+1}\le 3^m=f(m)$, the conditions for case 3 hold. The solution is $R(m)=\Theta(3^m)$. $T(n)=R(\log_3 n)=\Theta(n)$.
\end{description}

## Problem 4
\newcommand{\hy}{\text{-}}
The following algorithm takes $(A, l, r)$ and returns $(total, left, right, sum, left\hy left$, $left\hy right$, $left\hy sum$, $right\hy left$, $right\hy right$, $right\hy sum)$ where
\renewcommand{\thempfootnote}{\arabic{mpfootnote}}
\begin{minipage}{1\textwidth}
\begin{itemize}
\item $total=\sum_{i=l}^{r} A[i]$,
\item left, right, sum: $A[left, right]$ is the maximun subarray of $A[l, r]$, and $sum=\sum_{i=left}^{right} A[i]$,
\item left-left\footnote{left-left and right-right can be inferred from l and r. We keep them just for consistency.}, left-right, left-sum: the maximum subarray that must include the left end,
\item right-left, right-right\footnotemark[\value{mpfootnote}], right-sum: the maximum subarray that must include the right end.
\end{itemize}
\end{minipage}

And has a running time of $T(n)=2T(n/2)+O(1)$, or $T(n)=O(n)$.

\begin{algorithm}[H]
\caption*{FindMaximumSubarray($A, l, r$)}
\begin{algorithmic}[1]
    \If{$l = r$}
        \State \Return $(A[l], l, r, A[l], l, r, A[l], l, r, A[l])$
    \EndIf
    \State $mid=\lfloor (l + r) / 2 \rfloor$
    \State $(l\hy tot, l\hy l, l\hy r, l\hy sum, !l, l\hy l\hy r, l\hy l\hy sum, l\hy r\hy l, !mid, l\hy r\hy sum) = \text{FindMaximumSubarray}(A, l, mid)$
    \State $(r\hy tot, r\hy l, r\hy r, r\hy sum, !mid+1, r\hy l\hy r, r\hy l\hy sum, l\hy r\hy l, !r, r\hy r\hy sum) = \text{FindMaximumSubarray}(A, mid + 1, r)$
    \State $tot = l\hy tot + r\hy tot$
    \State $cross\hy sum = l\hy r\hy sum + r\hy l\hy sum$
    \If{$l\hy sum \geq r\hy sum$ and $l\hy sum \geq cross\hy sum$}
        \Comment {Choose the maximum subarray of left, right and cross}
        \State $sum = l\hy sum$
        \State $left = l\hy l$
        \State $right = l\hy r$
    \ElsIf{$r\hy sum \geq l\hy sum$ and $r\hy sum \geq cross\hy sum$}
        \State $sum = r\hy sum$
        \State $left = r\hy l$
        \State $right = r\hy r$
    \Else
        \State $sum = cross\hy sum$
        \State $left = l\hy r\hy l$
        \State $right = r\hy l\hy r$
    \EndIf
    \If{$l\hy l\hy sum \geq l\hy tot + r\hy l\hy sum$}
        \Comment {Choose the maximum subarray that must include the left end}
        \State $left\hy sum = l\hy l\hy sum$
        \State $left\hy right = l\hy l\hy r$
    \Else
        \State $left\hy sum = l\hy tot + r\hy l\hy sum$
        \State $left\hy right = r\hy l\hy r$
    \EndIf
    \If{$r\hy r\hy sum \geq r\hy tot + l\hy r\hy sum$}
        \Comment {Choose the maximum subarray that must include the right end}
        \State $right\hy sum = r\hy r\hy sum$
        \State $right\hy left = r\hy r\hy l$
    \Else
        \State $right\hy sum = r\hy tot + l\hy r\hy sum$
        \State $right\hy left = l\hy r\hy l$
    \EndIf
    \State \Return $(tot, left, right, sum, l, left\hy right, left\hy sum, right\hy left, r, right\hy sum)$
\end{algorithmic}
\end{algorithm}

## Problem 5
\begin{description}
\item[(a)] \quad
\begin{algorithm}[H]
\caption*{BinaryGCD($a, b$)}
\begin{algorithmic}[1]
    \If{$a = 0$}
        \State \Return $b$
    \EndIf
    \If{$b = 0$}
        \State \Return $a$
    \EndIf
    \If{$a$ is even and $b$ is even}
        \State \Return $2 \times \text{BinaryGCD}(a/2, b/2)$
    \ElsIf{$a$ is even and $b$ is odd}
        \State \Return $\text{BinaryGCD}(a/2, b)$
    \ElsIf{$a$ is odd and $b$ is even}  
        \State \Return $\text{BinaryGCD}(a, b/2)$
    \Else
        \If{$a \geq b$}
            \State \Return $\text{BinaryGCD}((a - b)/2, b)$
        \Else
            \State \Return $\text{BinaryGCD}((b - a)/2, a)$
        \EndIf
    \EndIf
\end{algorithmic}
\end{algorithm}
\item[(b)]
The worst-case running time of the binary GCD algorithm is $\Theta(n^2)$.

First we show that it is $O(n^2)$.
Let T(m) denote the running time of the binary GCD algorithm for two integers, where $m$ is the total number of bits in the inputs. In each step, we either divide one of the numbers by 2, or subtract one number from the other and then divide by 2. Each operation reduces the size of at least one of the numbers by at least 1 bit. Thus, we have:
$T(m)\le T(m-1)+O(m)$. Or $T(m)=O(m^2)$. The running time when $a$ and $b$ are $n$-bit integers is $T(2n)=O(n^2)$.

Then we show that it is $\Omega(n^2)$. Constructing a sequence $c_k$ where $c_0=0,c_1=1$ and $c_k=c_{k-1}+2c_{k-2}$ for $k\ge2$. It can be proved that $c_k=\frac{2^k-(-1)^k}{3}$ and $c_k$ has $k-1$ bits when $k\ge2$. Let $a=c_{n+1}$ and $b=c_n$. The calls to BinaryGCD will be: GCD($c_{n+1}, c_n$) $\to$ GCD($c_{n-1}, c_n$) $\to$ GCD($c_{n-1}, c_{n-2}$) $\to$ GCD($c_{n-3}, c_{n-2}$) $\to \cdots \to$ GCD($c_1, c_0$) $=$ GCD($1, 0$). A GCD($c_k, c_{k-1}$) takes $\Theta(k)$ time. So the total time is $\Theta(1+2+\cdots+n)=\Theta(n^2)$.

\end{description}

## Problem 6
\begin{description}
\item[(a)] Let $A=\begin{bmatrix}
a & b  \\
c & d  \\
\end{bmatrix}$. Then $A^2=\begin{bmatrix}
a\times a+b\times c & (a+d)\times b \\
(a+d)\times c & b\times c+d\times d \\
\end{bmatrix}$. Five multiplications $a\times a, b\times c, d\times d, (a+d)\times b, (a+d)\times c$ are used to compute $A^2$.
\item[(b)] Assume $M=\begin{bmatrix}
A & B  \\
C & D  \\
\end{bmatrix}$, where $A, B, C, D$ are $n/2\times n/2$ matrices. Then
$M^2=\begin{bmatrix}
AA+BC & AB+BD \\
CA+DC & CB+DD \\
\end{bmatrix}$ 
The recursive subproblems includes not only squaring but general matrix multiplications. And the matrix multiplication is not necessarily commutative. So we cannot use this divide-and-conquer method to reduce the number of multiplications.
\item[(c)] $AB+BA=(A+B)^2-A^2-B^2$. So we can compute $AB + BA$ through 3 matrix squaring in $3S(n)$ and 2 matrix addition in $O(n^2)$. The total time is $3S(n)+O(n^2)$.
\item[(d)] $AB+BA=\begin{bmatrix}
0 & XY  \\
0 & 0  \\
\end{bmatrix}$.
\item[(e)] First we construct $A=\begin{bmatrix}
X & 0  \\
0 & 0  \\
\end{bmatrix}$ and $B=\begin{bmatrix}
0 & Y  \\
0 & 0  \\
\end{bmatrix}$ in $O(n^2)$ time. Then we compute $AB+BA$ in $3S(2n)+O((2n)^2)$ time. Finally we extract $XY$ from the result in $O(n^2)$ time. The total time is $3S(2n)+O(n^2)$.

If $S(n)=O(n^c)$. Then $c\ge 2$. Because any general squaring algorithm must read all $n^2$ entries of the input matrix (suppose it does not read some $A_{i, j}$, then it will give the same output on, i.e., $I^2=I\neq (I+1_{i, j})^2=I+1_{i, j}+(1_{i, j})^2$). So the time for computing $XY$ is $3S(2n)+O(n^2)=3O((2n)^c)+O(n^2)=O(n^c)$.
\end{description}