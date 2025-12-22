---
title: ALG Problem Set 8
header-includes: |
  \usepackage{amsthm}
  \usepackage{amsmath}
  \usepackage{algorithm}
  \usepackage[noend]{algpseudocode}
  \usepackage{float}
  \usepackage{caption}
  \algrenewcommand\algorithmiccomment[1]{\hfill// #1}
---
\newcommand{\ta}[1]{\textsc{#1}}
## Problem 1
\begin{description}
\item[(a)] Suppose the $n$ keys are $1, 2, \ldots, n$. Suppose the number of collisions is
\#$1\le i < j\le n, h(i) = h(j)$. Then $E(\#i<j, h(i) = h(j)) = \sum_{1\le i < j\le n} \Pr(h(i) = h(j))$.
Since $h$ is uniformly random, $\Pr(i\neq j|h(i) = h(j)) = \frac{1}{m}$. Thus $E(\#i<j, h(i) = h(j)) = \sum_{1\le i < j\le n} \frac{1}{m} = \frac{n(n-1)}{2m}$.
\item[(b)] The probability that there is no collision is the probability that $h(1), h(2), \ldots, h(n)$ are all different. $h(1)$ can be any value in $\{0, 1, \ldots, m-1\}$. $h(2)$ can be any value in $\{0, 1, \ldots, m-1\} \setminus \{h(1)\}$, which has $m-1$ choices. Similarly, $h(3)$ has $m-2$ choices, and so on. Thus the probability of no collision is $\frac{m(m-1)(m-2)\cdots (m-n+1)}{m^n} = \frac{m!}{(m-n)!m^n}$.
\item[(c)] Let $p=\frac{m!}{(m-n)!m^n}$. The number of trials until the first success follows a geometric distribution: $E(\#trials) = \frac{1}{p} = \frac{(m-n)!m^n}{m!}$.
\item[(d)] The probability that a single trial fails is $1 - p$. Since the trials are independent, the probability that all $N$ trials fail is $(1 - p)^N = \left(1 - \frac{m!}{(m-n)!m^n}\right)^N$.
\item[(e)] We want $1-(1-p)^N \ge 1 - \frac{1}{n}$. Thus $(1-p)^N \le \frac{1}{n}$. Taking logarithm on both sides, we have $N \ln(1-p) \le -\ln n$. Since $\ln(1-p) \le -p$ for $0 < p < 1$, we have $N \ge \frac{\ln n}{- \ln(1-p)}\Leftarrow N \ge \frac{\ln n}{p} = \frac{(m-n)!m^n}{m!} \ln n$. Thus, if we choose $N = \left\lceil \frac{(m-n)!m^n}{m!} \ln n \right\rceil$, then the probability of at least one success in $N$ trials is at least $1 - \frac{1}{n}$.
\end{description}

## Problem 2
We augment the bit array $A$ with an integer $A.high$.
At the beginning, we set all bits in $A$ to 0 and set $A.high = 0$.

\ta{Increment}$(A)$
\begin{algorithmic}[1]
\State $i = 0$
\While{$i < A.length$ and $A[i] = 1$}
    \State $A[i] = 0$
    \State $i = i + 1$
\EndWhile
\If{$i < A.length$}
    \State $A[i] = 1$
    \State $A.high = \max(A.high, i + 1)$
\EndIf
\end{algorithmic}
\ta{Reset}$(A)$
\begin{algorithmic}[1]
\For{$i = 0$ to $A.high - 1$}
    \State $A[i] = 0$
\EndFor
\State $A.high = 0$
\end{algorithmic}

Correctness:
\ta{Increment} is the same as the original version except that we update $A.high$ when we set a bit to 1. Thus it is correct.
We shall show that \ta{Increment} and \ta{Reset} maintains the property that all bits with index $\ge A.high$ are 0. Initially, $A.high = 0$ and the property holds. In line 1-4 of \ta{Increment}, we set some bits to 0, so the property still holds. In line 5-7, if we set $A[i]$ to 1. Since $j\ge \max(A.high, i + 1) \to j\ge A.high \land j\neq i$, after updating $A.high$, all bits with index $\ge A.high$ are still 0. (...)Thus \ta{Reset} is correct and preserves the property.

Running time: the actual cost of \ta{Increment} is bounded by the number of bit flipped. And the actual cost of \ta{Reset} is $A.high$. We assign amortized costs as follows:
\begin{tabular}{lc}
\ta{Increment} & $3$ \\
\ta{Reset} & $0$ \\
flipping a bit from 0 to 1 & $2$ \\
flipping a bit from 1 to 0 & $0$ \\
\end{tabular}
The correctness of the amortized costs for flipping bits is proved in text book.
In \ta{Increment}, we pay 2 credits to flip $A[i]$ to 1 and store the remaining 1 credit in $A.high$. We shall show that $A.high$ increases by at most 1. Assume otherwise $i > A.high$ before line 7. Then $A[i]=0$ by the property we proved above, which contradicts the condition of the while loop $i = A.length \lor A[i] = 1$ and the condition of the if statement $i < A.length$. Therefore, we can store 1 credit in each unit of $A.high$. In \ta{Reset}, we use the credits stored in $A.high$ to pay for the actual cost. Therefore, any sequence of $n$ \ta{Increment} and \ta{Reset} operations takes $O(n)$ time in total.

## Problem 3
First we compute the actual cost of \ta{Decimate}. Since $\sum_{i=0}^{n} [i \mod 10 = 0] = \lceil \frac{n}{10} \rceil$. There are $\lceil \frac{n}{10} \rceil$ times executing line 4 and $n - \lceil \frac{n}{10} \rceil$ times executing line 6. Thus the actual cost is $1 \cdot \lceil \frac{n}{10} \rceil + 2\cdot (n - \lceil \frac{n}{10} \rceil) = \lfloor 1.9n \rfloor$,
where the actual cost of \ta{Push} and \ta{Pull} are 1.
\begin{tabular}{|c|c|c|}
\hline
Operation & Actual Cost & Size Change \\ \hline
\ta{Push} & $1$ & $+1$ \\ \hline
\ta{Pull} & $1$ & $-1$ \\ \hline
\ta{Decimate} & $\lfloor 1.9n \rfloor$ & $-\lceil \frac{n}{10} \rceil$ \\ \hline
\end{tabular}
Then we assign amortized costs as follows:
\begin{tabular}{lc}
\ta{Push} & $20$ \\
\ta{Pull} & $0$ \\
\ta{Decimate} & $0$ \\
\end{tabular}
We shall now show that we can pay for any sequence of operations with these amortized costs. When we \ta{Push}, we pay the actual cost of $1$ and store $19$ credits on the newly added element. When we \ta{Pull}, we pay the actual cost of $1$ using the $19$ credits stored on the removed element. When we \ta{Decimate}, we need to pay an actual cost of at most $1.9n$. Since there are at least $0.1n$ elements being removed, there are at least $1.9n$ credits stored on these elements, which is sufficient to pay for the actual cost of \ta{Decimate}. Thus, all actual costs can be paid for by the amortized costs, and the amortized cost of each operation is $O(1)$.

## Problem 4
The running time of \ta{GoodView} is $\Theta(n)$. First we prove it is $\Omega(n)$. Since line 5 executes $n$ times and each execution costs 1, the total cost of line 5 is $n$. Thus the running time is $\Omega(n)$.

Next we prove it is $O(n)$. Assume in each iteration of the for loop, \ta{Pop} executes $t_i$ times. Then the while conditional statement runs $t_i+1$ times. We shall show that $\sum_{i=1}^{n} t_i \le n$. Note that $S$ is always non-empty before line 4. Each execution of \ta{Pop} removes one element from $S$. Since there are $n$ elements \ta{Push}ed into $S$ in total, line 4 can execute at most $n$ times. Thus $\sum_{i=1}^{n} t_i \le n$. Since each execution of line 4 costs 1, the total cost of line 4 is at most $n$. Line 3 costs $\sum_{i=1}^{n} (t_i+1) = O(n)$. All other lines cost $O(n)$ in total. Thus the running time is $O(n)$.

## Problem I.1
We simply use array to store the elements in the multiset. We use \ta{Select}, the median-of-medians algorithm to find the $k$-th smallest element in worst-case $O(n)$ time.

\ta{Insert}$(S, x)$
\begin{algorithmic}[1]
\State $S.append(x)$
\end{algorithmic}

\ta{DeleteLargeHalf}$(S)$
\begin{algorithmic}[1]
\State Initialize an empty array $S'$
\State $k = \lfloor \frac{S.size}{2} \rfloor$
\State $m = $ \ta{Select}$(S, k + 1)$
\For{each element $e$ in $S$}
    \If{$e < m$}
        \State $S'.append(e)$
    \EndIf
\EndFor
\While{$S'.size < k$}
    \State $S'.append(m)$
\EndWhile
\State Replace $S$ with $S'$
\end{algorithmic}

\ta{Print}$(S)$
\begin{algorithmic}[1]
\For{each element $e$ in $S$}
    \State Print $e$
\EndFor
\end{algorithmic}

\ta{DeleteLargeHalf} takes $O(n)$ for \ta{Select}, $O(n)$ for the for loop and $O(k) = O(n)$ for the while loop. Thus its worst-case running time is $O(n)$. We use $cn$ to denote the actual cost of \ta{DeleteLargeHalf} for some constant $c > 0$. Since \ta{DeleteLargeHalf} reduces $\lceil \frac{n}{2} \rceil$ elements, we store $2c$ credits per element in the multiset. Thus the amortized cost of \ta{Insert} is $1 + 2c$ and \ta{DeleteLargeHalf} is $0$. Therefore, any sequence of $n$ operations takes $O(|S|)$ time in total.

## Problem I.2
We use 3 stacks $S1, S2$ and $S3$ and variables $n_1, n_2$. After each operation, the auxiliary stacks $S3$ is empty. Suppose the elements in the \textit{quack} are $a_1, a_2, \ldots, a_n$ from left to right. Then for some $0\le k\le n$, $S1$ contains $a_1, a_2, \ldots, a_k$ and $S2$ contains $a_n, a_{n-1}, \ldots, a_{k+1}$, both from top to bottom ($k = 0$ or $n$ yields an empty stack). $n_1$ and $n_2$ store the sizes of $S1$ and $S2$ respectively.

\ta{QuackPush}$(x)$
\begin{algorithmic}[1]
\State $S1$.push$(x)$
\State $n_1 = n_1 + 1$
\end{algorithmic}

\ta{QuackPop}()
\begin{algorithmic}[1]
\If{$n_1 > 0$}
    \State $n_1 = n_1 - 1$
    \State \Return $S1$.pop$()$
\EndIf
\If{$n_2 = 0$}
    \State \Return NULL
\EndIf
\For{$i = 1$ to $\lfloor \frac{n_2}{2} \rfloor$}
    \State $\ta{Push}(S3, \ta{Pop}(S2))$
\EndFor
\For{$i = \lfloor \frac{n_2}{2} \rfloor + 1$ to $n_2$}
    \State $\ta{Push}(S1, \ta{Pop}(S2))$
\EndFor
\For{$i = 1$ to $\lfloor \frac{n_2}{2} \rfloor$}
    \State $\ta{Push}(S2, \ta{Pop}(S3))$
\EndFor
\State $n_1 = \lceil \frac{n_2}{2} \rceil - 1$
\State $n_2 = \lfloor \frac{n_2}{2} \rfloor$
\State \Return \ta{Pop}$(S1)$
\end{algorithmic}

\ta{QuackPull}()
\begin{algorithmic}[1]
\If{$n_2 > 0$}
    \State $n_2 = n_2 - 1$
    \State \Return $S2$.pop$()$
\EndIf
\If{$n_1 = 0$}
    \State \Return NULL
\EndIf
\For{$i = 1$ to $\lfloor \frac{n_1}{2} \rfloor$}
    \State $\ta{Push}(S3, \ta{Pop}(S1))$
\EndFor
\For{$i = \lfloor \frac{n_1}{2} \rfloor + 1$ to $n_1$}
    \State $\ta{Push}(S2, \ta{Pop}(S1))$
\EndFor
\For{$i = 1$ to $\lfloor \frac{n_1}{2} \rfloor$}
    \State $\ta{Push}(S1, \ta{Pop}(S3))$
\EndFor
\State $n_2 = \lceil \frac{n_1}{2} \rceil - 1$
\State $n_1 = \lfloor \frac{n_1}{2} \rfloor$
\State \Return \ta{Pop}$(S2)$
\end{algorithmic}
The upper bound of actual cost of \ta{QuackPull} is
$c_i \le
\begin{cases}
1 & n_2 > 0 \\
1 + 3n_1 & n_2 = 0, n_1 > 0 \\
1 & n_2 = 0, n_1 = 0
\end{cases}$.

Let the potential function $\Phi = 3|n_1 - n_2|$. Initially $\Phi = 0$. We compute the amortized cost $a_i = c_i + \Phi_i - \Phi_{i-1}$.
\begin{itemize}
\item If $n_2 > 0$, then $a_i = 1 + 3|n_1 - (n_2 - 1)| - 3|n_1 - n_2| \le 4$.
\item If $n_2 = 0, n_1 > 0$, then $a_i \le 1 + 3n_1 + 3|\lceil \frac{n_1}{2} \rceil - 1 - \lfloor \frac{n_1}{2} \rfloor| - 3n_1 \le 4$.
\item If $n_2 = 0, n_1 = 0$, then $a_i = 1 + 0 - 0 = 1$.
\end{itemize}
Thus the amortized cost of \ta{QuackPull} is $O(1)$. Similarly, the amortized cost of \ta{QuackPop} is also $O(1)$. The amortized cost of \ta{QuackPush} is $1 + 3|(n_1 + 1) - n_2| - 3|n_1 - n_2| \le 4$.