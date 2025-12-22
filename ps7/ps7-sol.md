---
title: ALG Problem Set 7
header-includes: |
  \usepackage{amsthm}
  \usepackage{amsmath}
  \usepackage{algorithm}
  \usepackage[noend]{algpseudocode}
  \usepackage{float}
  \usepackage{caption}
  \usepackage{tikz}
  \usetikzlibrary{arrows}
  \algrenewcommand\algorithmiccomment[1]{\hfill// #1}
---
\newcommand{\ta}[1]{\textsc{#1}}
\tikzset{
  treenode/.style = {align=center, inner sep=0pt, text centered,
    font=\sffamily},
  arn_null/.style = {treenode, rectangle, white,
    minimum width=0.5em, minimum height=1.5em, fill=black},% arbre rouge noir, nil
  arn_n/.style = {treenode, circle, white, font=\sffamily\bfseries, draw=black,
    fill=black, text width=1.5em},% arbre rouge noir, noeud noir
  arn_r/.style = {treenode, circle, red, draw=red, 
    text width=1.5em, very thick},% arbre rouge noir, noeud rouge
  arn_x/.style = {treenode, rectangle, draw=black,
    minimum width=0.5em, minimum height=0.5em}% arbre rouge noir, nil
}

## Problem 1
\textbf{(a)}
\begin{figure}[H]
\begin{tikzpicture}[->,>=stealth',level/.style={level distance = 1cm}] 
\node [arn_n] {87}; 
\end{tikzpicture}
[87]\quad
\begin{tikzpicture}[->,>=stealth',level/.style={level distance = 1cm}] 
\node [arn_n] {87}
  child{ node [arn_r] {75}}
  child{ node [arn_x] {}};
\end{tikzpicture}
\quad [87, 75]
\begin{tikzpicture}[->,>=stealth',level/.style={level distance = 1cm}] 
\node [arn_n] {75}
  child{ node [arn_r] {62}}
  child{ node [arn_r] {87}};
\end{tikzpicture}
[87, 75, 62]\quad

\begin{tikzpicture}[->,>=stealth',level/.style={level distance = 1cm}] 
\node [arn_n] {75}
  child{ node [arn_n] {62}
    child{ node [arn_r] {20}}
    child{ node [arn_x] {}}
  }
  child{ node [arn_n] {87}};
\end{tikzpicture}
[87, 75, 62, 20]\quad
\begin{tikzpicture}[->,>=stealth',level/.style={level distance = 1cm}] 
\node [arn_n] {75}
  child{ node [arn_n] {38}
    child{ node [arn_r] {20}}
    child{ node [arn_r] {62}}
  }
  child{ node [arn_n] {87}};
\end{tikzpicture}
[87, 75, 62, 20, 38]

\begin{tikzpicture}[->,>=stealth',level/.style={level distance = 1cm}] 
\node [arn_n] {75}
  child{ node [arn_r] {38}
    child{ node [arn_n] {20}
      child{ node [arn_r] {9}  }
      child{ node [arn_x] {}  }
    }
    child{ node [arn_n] {62}}
  }
  child{ node [arn_n] {87}};
\end{tikzpicture}
[87, 75, 62, 20, 38, 9]
\end{figure}
\textbf{(b)}
\begin{figure}[H]
\begin{tikzpicture}[->,>=stealth',level/.style={level distance = 1cm}] 
\node [arn_n] {75}
  child{ node [arn_r] {38}
    child{ node [arn_n] {20}}
    child{ node [arn_n] {62}}
  }
  child{ node [arn_n] {87}};
\end{tikzpicture}
[9]\quad
\begin{tikzpicture}[->,>=stealth',level/.style={level distance = 1cm}] 
\node [arn_n] {75}
  child{ node [arn_n] {38}
    child{ node [arn_x] {}}
    child{ node [arn_r] {62}}
  }
  child{ node [arn_n] {87}};
\end{tikzpicture}
[9, 20]\quad
\begin{tikzpicture}[->,>=stealth',level/.style={level distance = 1cm}] 
\node [arn_n] {75}
  child{ node [arn_n] {62}}
  child{ node [arn_n] {87}};
\end{tikzpicture}
[9, 20, 38]


\begin{tikzpicture}[->,>=stealth',level/.style={level distance = 1cm}] 
\node [arn_n] {75}
  child{ node [arn_x] {}}
  child{ node [arn_r] {87}};
\end{tikzpicture}
[9, 20, 38, 62]\quad
\begin{tikzpicture}[->,>=stealth',level/.style={level distance = 1cm}] 
\node [arn_n] {87};
\end{tikzpicture}
[9, 20, 38, 62, 75]\quad
\begin{tikzpicture}[->,>=stealth',level/.style={level distance = 1cm}] 
\node [arn_null] {NIL};
\end{tikzpicture}
[9, 20, 38, 62, 75, 87]
\end{figure}

## Dynamic order statistics trees
CLRS 14.1 have discussed how to augment a red-black tree to support the operation \ta{OS-Select} in $O(\lg n)$ time, which returns the $i$-th smallest element in the tree.
We further write a function \ta{OS-Key-Rank}$(T, k)$ to return then rank of $k$ in the dynamic set represented by $T$ (the number of elements less than $k$ in $T$, plus one) in $O(\lg n)$ time (Ex 14.1-4).

\ta{OS-Key-Rank}$(T, k)$
\begin{algorithmic}[1]
\State $r = 1$
\State $p = T.root$
\While{$p \neq T.nil$}
    \If{$k < p.key$}
        \State $p = p.left$
    \ElsIf{$k > p.key$}
        \State $r = r + p.left.size + 1$
        \State $p = p.right$
    \Else
        \State $r = r + p.left.size$
        \State $p = T.nil$ \Comment{synonym for break}
    \EndIf
\EndWhile
\State \Return $r$
\end{algorithmic}

\ta{OS-Key-Rank} maintains the following invariant: at the start of each iteration of the \textbf{while} loop, let $T(p)$ be the subtree rooted at $p$, $R(p)$ be the rank of $k$ in $T(p)$, then $r = R(T) - R(p) + 1$.

Initially, $p$ is the root of $T$, so $R(p) = R(T)$ and thus $r = 1 = R(T) - R(p) + 1$.

If $k < p.key$, then $\forall x \in T(p), x < k \iff x\in T(p.left) \land x < k$. Thus, $R(p)=R(p.left)$, so after updating $p$ to $p.left$, the invariant still holds.

If $k > p.key$, then $\forall x \in T(p), x < k \iff x\in T(p.left) \lor x = p \lor x\in T(p.right) \land x < k$. Thus, $R(p)=R(p.right) + p.left.size + 1$, so after updating $r$ and $p$, $r + R(p)$ becomes $r + p.left.size + 1 + R(p.right) = r + R(p)$. The invariant still holds.

If $k = p.key$, $R(p) = p.left.size + 1$. $r + R(p)$ becomes $r + p.left.size + R(null) = r + R(p)$. The invariant still holds.

When the loop ends, $p = null$, $R(p) = 1$. Thus, $r = R(T) - R(p) + 1 = R(T)$. We return $r$ as desired. \qed

The height of the tree is $O(\lg n)$, and each iteration takes $O(1)$ time, so the total time is $O(\lg n)$.

## Problem 2
We use order statistics tree to solve this problem. To initialize the data structure, we simply return an empty tree.

\ta{Insert}$(T, k)$
\begin{algorithmic}[1]
\State \textbf{call} \ta{OS-Insert}$(T, k)$
\end{algorithmic}

\ta{Median}$(T)$
\begin{algorithmic}[1]
    \State \Return \ta{OS-Select}$(T, \lceil T.size/2 \rceil)$
\end{algorithmic}

## Problem 3
We also use order statistics tree to solve this problem. The set represented by the tree contains all the available rooms.

\ta{Initialize}$(n)$
\begin{algorithmic}[1]
\State $T = $ new order statistics tree
\For{$i = 1$ to $n$}
    \State \ta{OS-Insert}$(T, i)$
\EndFor
\State \Return $T$
\end{algorithmic}

The running time is $O(n \lg n)$, which is polynomial time.

The operations bellow just call constant times of \ta{OS-Insert}, \ta{OS-Delete}, \ta{OS-Select} and \ta{OS-Key-Rank}, each of which takes $O(\lg n)$ time, so the time complexity of each operation is $O(\lg n)$.

\ta{Count}$(T, l, r)$
\begin{algorithmic}[1]
\State \Return $\ta{OS-Key-Rank}(T, r + 1) - \ta{OS-Key-Rank}(T, l)$
\end{algorithmic}

The number of available rooms in $[l, r]$ is # of available rooms $\le r$ minus # of available rooms $< l$. Given by $rank(r + 1) - 1$ and $rank(l) - 1$ respectively. \qed

\ta{CheckIn}$(T, l, h)$
\begin{algorithmic}[1]
\State $rank = $ \ta{OS-Key-Rank}$(T, l)$
\If{$rank > T.size$}
    \State \Return $NULL$
\EndIf
\State $room = $ \ta{OS-Select}$(T, rank)$
\If{$room > h$}
    \State \Return $NULL$
\Else
    \State \ta{OS-Delete}$(T, room)$
    \State \Return $room$
\EndIf
\end{algorithmic}

Assume there is an available room in $[l, h]$. Let $r$ denotes the smallest available room $\ge l$. Then any available room in $[1, l-1]$ is smaller than $r$, and any available room in $[l, n]$ is larger than or equal to $r$. Thus, $rank(l) = rank(r)\le T.size$. We have $room = r$. \ta{CheckIn} works correctly.

Otherwise, there is no available room in $[l, h]$.
If there is no available room $\ge l$, then $rank(l) > T.size$.
If there is an available room $\ge l$, then by same reasoning, $room$ is the smallest available room $\ge l$. Since there is no available room in $[l, h]$, $room > h$. \ta{CheckIn} returns $NULL$ correctly. \qed

\begin{minipage}{\textwidth}
\ta{CheckOut}$(T, x)$
\begin{algorithmic}[1]
\State \ta{OS-Insert}$(T, x)$
\end{algorithmic}
\end{minipage}

## Problem 4
\textbf{(a)} Since
```c
$ bc
scale=10
61*(sqrt(5)-1)/2
37.7000733107
62*(sqrt(5)-1)/2
38.3181072994
63*(sqrt(5)-1)/2
38.9361412881
64*(sqrt(5)-1)/2
39.5541752768
65*(sqrt(5)-1)/2
40.1722092655
```
, we have

| $k$    | 61 | 62 | 63 | 64 | 65 |
|:---:   |:--:|:--:|:--:|:--:|:--:|
| $h(k)$ | 700 | 318 | 936 | 554 | 172 |
\begin{description}
\item[(b)] Assume $x = c_n c_{n-1} \ldots c_1$, where each $c_i$ is a character. Then $h(x) = \sum_{i=1}^{n} h(c_i) \cdot (2^{p})^{i-1} \mod m = \sum_{i=1}^{n} h(c_i) \mod m$.
If we can derive $y$ by permuting the characters of $x$, then $y$ also has the same multiset of characters as $x$, and thus $h(y) = \sum_{i=1}^{n} h(c_i) \mod m = h(x)$.
\end{description}

## Problem 5
\begin{description}
\item[(a)]
\begin{flalign*}
Q_k &= {n \choose k} \left(\frac{1}{n}\right)^k \left(\frac{n-1}{n}\right)^{n-k} & \\
&\le {n \choose k} / n^k & \\
&= \frac{n(n-1)(n-2)\ldots(n-k+1)}{k! \cdot n^k} & \\
&< \frac{n^k}{k! \cdot n^k} = \frac{1}{k!} & \\
\end{flalign*}
Since $e^k = \sum_{i=0}^{\infty} \frac{k^i}{i!}$. The sum is larger than $k$th term $\frac{k^k}{k!}$. Thus, $\frac{1}{k!} < \frac{e^k}{k^k}$ and we have $Q_k < \frac{e^k}{k^k}$.
\item[(b)] Let $X_{i,k}$ be the event that the $i$-th slot has exactly $k$ keys. Then $P_k = \Pr\left(M\le k \cap \bigcup_{i=1}^{n} X_{i,k}\right) \le \sum_{i=1}^{n} \Pr(X_{i,k}) = n Q_k$. Thus, by (a), $P_k \le n \cdot \frac{e^k}{k^k}$.
\item[(c)] Assume $m = \ln n$.
For $k\ge \frac{c\ln n}{\ln \ln n} = \frac{m}{\ln m}$. Since $\frac{m}{\ln m}\ge e$, $k\ge c\cdot e$.

By calculus, $f(x) = k - k\ln k$ is monotonically decreasing as $k \ge 1$. Thus, for some constant $c > 1$,
\begin{flalign*}
\ln (n^2P_k) &\le \ln \left(n^2 \cdot n \cdot \frac{e^k}{k^k}\right) & \\
&\le 3m + k - k \ln k& \\
&\le 3m + \frac{cm}{\ln m} - \frac{cm}{\ln m} \ln \frac{cm}{\ln m} & \\
&\le -\frac{m}{\ln m} ((c-3)\ln m+c\ln c-c\ln \ln m-c) &\\
&\le 0 \quad \text{(when $c = 4$ and $n$ is sufficiently large)} & \tag{1} \\
\end{flalign*}
(1): $c = 4$, the expression in the bracket is $\ln m + 4\ln 4 - 4\ln \ln m - 4$. Let $g(x) = x + 4\ln 4 - 4\ln x - 4$. $g'(x) = 1 - \frac{4}{x}$. $g'(x) \ge 0$ if and only if $x\ge 4$. So $g(x)\ge g(4) = 4 + 4\ln 4 - 4\ln 4 - 4 = 0$.

Thus, $P_k \le \frac{1}{n^2}$ for $k \ge \frac{4\ln n}{\ln \ln n}$. And there exists $c$ such that for $k \ge \frac{c\lg n}{\lg \lg n}$, $P_k \le \frac{1}{n^2}$.
\item[(d)]
\begin{flalign*}
E(M) &= \sum_{k=1}^{n} k \cdot \Pr(M = k) & \\
&= \sum_{k=1}^{n} k P_k & \\
&= \sum_{k=1}^{\lfloor \frac{c\lg n}{\lg \lg n} \rfloor} k P_k + \sum_{k=\lceil \frac{c\lg n}{\lg \lg n} \rceil}^{n} k P_k & \\
&\le \frac{c\lg n}{\lg \lg n} \sum_{k=1}^{\lfloor \frac{c\lg n}{\lg \lg n} \rfloor} P_k + n \cdot n \frac{1}{n^2} & \\
&\le \frac{c\lg n}{\lg \lg n} \cdot 1 + 1 & \\
&= O\left(\frac{\lg n}{\lg \lg n}\right)
\end{flalign*}
\end{description}

## Bonus Problem

Assume the keys are $x_1, x_2, \ldots, x_n$, in sorted order. Let $d_i$ be the depth of the node with key $x_i$ in the loose treap. We prove that $E(d_i) = O(\lg n)$ for each $i$.

We define i.r.v. $X_{i,j} = I$ \{if $x_j$ is an ancestor of $x_i$ in the loose treap\}.

$d_i = \sum_{j=1}^{n} X_{i,j}$

First we show that $X_{i,j}=1$ implies that $x_j.priority \ge x_i.priority$, and, for every $k$ such that $i < k < j$ or $j < k < i$, $x_j.priority \ge x_k.priority$. (See CLRS Problem 13-4.f).

The left branch of the theorem is trivial by heap property. For the right branch, if there exists $k$ such that $i < k < j$ or $j < k < i$ and $x_k.priority > x_j.priority$, then $x_k$ would be inserted into the treap before $x_i$ and $x_j$. Since $x_i < x_k < x_j$ or $x_j < x_k < x_i$, $x_i$ and $x_j$ would be in the different subtrees of $x_k$, contradicting the assumption that $x_j$ is an ancestor of $x_i$.

Thus, $\Pr(X_{i,j}=1)\le \Pr(x_j.priority$ is the largest among $\{x_k.priority | i \le k < j \text{ or } j < k \le i\})$. This probability only depends on $k = |j - i|$. Assume the probability is $q_k$. Since priorities are independent and geometrically distributed, $q_k = \sum_{m=1}^{\infty} \Pr(x_j.priority = m) \cdot \Pr(l$s other priorities $\le m) = \sum_{m=1}^{\infty} \frac{1}{2^m} \cdot \left(1 - \frac{1}{2^m}\right)^l$.

Then, we bound $q_k$: there exists a constant $C$ such that for all $k$, $q_k \le \frac{C}{k}$.

First, we notice that $$\left(1 - \frac{1}{2^m}\right)^k \le e^{-k/2^m},$$
so
$$q_k \le \sum_{m=1}^{\infty} \frac{1}{2^m} e^{-k/2^m} = r(k).$$
Let $M = \lfloor \lg k \rfloor$. For $k\ge 4$, we split the sum into two parts:
$$r(k) = \sum_{m=1}^{M-1} \frac{1}{2^m} e^{-k/2^m} + \sum_{m=M}^{\infty} \frac{1}{2^m} e^{-k/2^m}.$$
For the second part,
$$\sum_{m=M}^{\infty} \frac{1}{2^m} e^{-k/2^m} \le \sum_{m=M}^{\infty} \frac{1}{2^m} = \frac{1}{2^{M-1}} \le \frac{4}{k}.$$
For the first part, it can be shown that $\frac{1}{2^m} e^{-k/2^m}$ is monotonically increasing when $m \le M$.
Thus,
$$\sum_{m=1}^{M-1} \frac{1}{2^m} e^{-k/2^m}
\le \int_{1}^{M} \frac{1}{2^x} e^{-k/2^x} \,\mathrm{d}x
\le -\int_{1}^{k/2} \frac{u}{k} e^{-u} \,\mathrm{d}\left(\lg\frac{k}{u}\right)
\le \frac{1}{k\ln 2} \int_{1}^{\infty} e^{-u} \,\mathrm{d}u = \frac{1}{e\ln 2}\cdot \frac{1}{k},$$
where we use substitution $u = k/2^x$.

Thus, for $k\ge 4$, $r(k) \le \left(4 + \frac{1}{e\ln 2}\right) \cdot \frac{1}{k}$. For $k < 4$, we can choose a sufficiently large constant $C$ such that $r(k) \le \frac{C}{k}$.

Finally, we have
$$E(d_i) = \sum_{j=1}^{n} E(X_{i,j}) = \sum_{j=1}^{n} \Pr(X_{i,j}=1) \le \sum_{j=1}^{n} q_{|j-i|}
\le 2 \sum_{k=1}^{n-1} \frac{C}{k} = O(\lg n).\quad \text{(the harmonic series)}
$$

Hence, the expected depth of each node is $O(\lg n)$.

## Acknowledgements
I use [this url](https://texample.net/red-black-tree/) to draw red-black trees.

AI helps me find $1/k$ bound in Bonus Problem. [url](https://chat.deepseek.com/share/wcxq6ggztv1okddu2s)