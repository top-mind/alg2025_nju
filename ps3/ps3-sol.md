---
title: ALG Problem Set 3
header-includes: |
  \usepackage{amsthm}
  \usepackage{algorithm}
  \usepackage[noend]{algpseudocode}
  \usepackage{float}
  \usepackage{caption}
  \algrenewcommand\algorithmiccomment[1]{\hfill// #1}
---
## Problem 1
\begin{description}
\item[(a)] Maintain a set of candidate numbers $C$. Initially $C=\{1,2,\ldots,n\}$. For each question, we evenly divide $C$ into two subsets $C_1$ and $C_2$ (if $|C|$ is odd, let $|C_1|=|C_2|+1$). Ask the question "Is the number in $C_1$?". If the answer is "Yes", let $C=C_1$, otherwise let $C=C_2$. Repeat this process until $|C|=1$. The remaining number in $C$ is the answer. Since each question halves the size of $C$, we need at most $\lceil \log_2 n \rceil$ questions.

Note: This strategy is optimal because each question can be viewed as a binary partition of the current candidate set, and to minimize the worst-case number of questions, we should always split the set as evenly as possible.
\item[(b)] If $n$ is unknown, it is hard to determine the optimal strategy. However, we can use an exponential search strategy to find an upper bound for the target integer and then apply the binary search strategy. We can ask questions in the following manner:
\begin{itemize}
\item For the $i$-th question ($i=1,2,\ldots$), ask "Is the number in $[2^{i-1}, 2^i-1]$?" If "Yes", we can let $C \gets [2^{i-1}, 2^i-1]$ and proceed to binary search within this range. If "No", continue to the next $i$.
\end{itemize}
If the chosen integer is $x$, we will find the range $[2^{k-1}, 2^k-1]$ such that $2^{k-1} \leq x < 2^k$ after $k$ questions, where $k = \lfloor \log_2 x \rfloor+1$. Then we can perform binary search within this range, which will take at most $\lceil \log_2 (2^k - 2^{k-1}) \rceil = k - 1$ questions. Therefore, the total number of questions asked is at most $k + (k - 1) = 2k - 1 = 2\lfloor \log_2 x \rfloor + 1$.
\end{description}
## Problem 2
\begin{description}
\item[(a) (b)] The answer to (b) is yes. We can find the smallest integer in $[1..m]$ that is not present in $A$ within $O(\log n)$ time using a binary search approach. The algorithm is as follows:
\begin{itemize}
\item Initialize two pointers: $low = 1$ and $high = n+1$. By the pigeonhole principle, the smallest missing integer must be in the range $[1..n+1]$.
\item While $low < high$:
\begin{itemize}
\item Let $mid = \lfloor (low + high) / 2 \rfloor$.
\item If $a[mid] = mid$, then $a[1..mid] = [1..mid]$. The smallest missing integer must be in the right half. Set $low = mid + 1$.
\item Otherwise, the smallest missing integer is in the left half. Set $high = mid$
\end{itemize}
\item The smallest missing integer is the value of $low$ after the loop ends.
\end{itemize}
This is a standard binary search algorithm, which runs in $O(\log n)$ time.
\end{description}
## Problem 3
The algorithm \textsc{FindKth}$(A, B, k)$ takes two sorted arrays $A$, $B$, an integer $1\le k\le |A|+|B|$, and returns the $k$-th smallest element in the array $A + B$. The runnning time is $O(\log k)=O(\log(|A|+|B|))$. For our question, we can call \textsc{FindKth}$(A, B, (|A|+|B|)/2)$ to get the median of $A+B$ in $O(\log(|A|+|B|))$ time.

\begin{minipage}{\columnwidth}
\renewcommand\thempfootnote{\arabic{mpfootnote}}
// The initial call is \textsc{FindKth}$(A, B, n, m, (n+m)/2)$\\
\textsc{FindKth}$(A, B, n, m, k)$
\begin{algorithmic}[1]
\If{$k=1$}
    \State \Return $\min(A[1], B[1])$
\EndIf
\State $mid1 = \lfloor k/2 \rfloor$
\State $mid2 = k - mid1$
\State $a_{mid} = mid1 \le n\ \text{?}\,A[mid1] : \infty$
\State $b_{mid} = mid2 \le m\ \text{?}\,B[mid2] : \infty$
\If{$a_{mid} \le b_{mid}$}
  \State \Return FindKth(A[mid1+1:]\footnote{We just pass the starting index of the subarray instead of creating a new one.}, B, n-mid1, m, k-mid1)
\Else
  \State \Return FindKth(A, B[mid2+1:], n, m-mid2, k-mid2)
\EndIf
\end{algorithmic}
\end{minipage}
For the correctness, we first prove when all elements in $A$ and $B$ are distinct.
Assume the $k$-th smallest element is $x$:
\begin{itemize}
\item If $A[mid1] < B[mid2]$, then $x$ must $> A[mid1]$. Otherwise, if $x \le A[mid1]$, then there are at most $mid1$ elements in $A$ and at most $mid2-1$ elements in $B$ that are not greater than $x$, which means there are at most $mid1+(mid2-1) = k-1$ elements not greater than $x$. This contradicts the definition of $x$. Similarly, if $A[mid1] > B[mid2]$, then $x > B[mid2]$.
\item Note that if we remove a number $y < x$, then $x$ is the $(k-1)$-th smallest element in the new array. If $A[1..mid1]$ all less than $x$, we can remove them all. Similarly, if $B[1..mid2]$ all less than $x$, we can remove them all (corresponding to line 8 and 10 respectively).
\end{itemize}
What if there are duplicates? Let $A'[i]=(A[i], i)$ and $B'[i]=(B[i], n + i)$ be the augmented arrays. We can apply the same algorithm on $A'$ and $B'$. Since $A'$ and $B'$ are distinct, we can find the $k$-th smallest element $(x, j)$ in $A'+B'$. However, $A'[i] < B'[j]\iff A[i]\le B[j]$. So the algorithm can be applied directly on $A$ and $B$ without any modification.

The running time $T(k)$ satisfies the recurrence:
$T(k) = T(\lceil k/2\rceil) + O(1)$

So $T(k)=O(\log k)$.

## Problem 4
\begin{description}
\item[(a)] Given player $i$, query the other $n-1$ players. Player $i$ is citizen if and only if at least $\lfloor n/2 \rfloor$ of them say player $i$ is citizen. The initial call is \textsc{IsCitizen}$([1, 2,\ldots,n], i)$.

\begin{minipage}{\columnwidth}
\textsc{IsCitizen}$(A[1..n], i)$
\begin{algorithmic}[1]
\State $count = 0$
\For{$j = 1$ to $n$}
  \If{$A[j] \ne i$}
    \If{player $A[j]$ says player $i$ is citizen}
      \State $count = count + 1$
    \EndIf
  \EndIf
\EndFor
\If{$count \ge \lfloor n/2 \rfloor$}
  \State \Return \texttt{true}
\Else
  \State \Return \texttt{false}
\EndIf
\end{algorithmic}
\end{minipage}\\[2ex]
Since \#citizens > \#werewolves, \#citizens $\ge \lfloor n/2 \rfloor+1$.
If player $i$ is a citizen, there are at least $\lfloor n/2 \rfloor$ citizens among the other $n-1$ players, so at least $\lfloor n/2 \rfloor$ players will tell the truth and say player $i$ is a citizen. If player $i$ is a werewolf, there are at most $n-\lfloor n/2 \rfloor-2=\lceil n/2 \rceil - 2$ werewolves among the other $n-1$ players, so at most $\lceil n/2 \rceil - 2$ players will lie and say player $i$ is a citizen. Since $\lfloor n/2 \rfloor \ge \lceil n/2 \rceil - 1 > \lceil n/2 \rceil - 2$, the algorithm is correct.
\item[(b)] We can develop an algorithm that guarranteed to return a citizen when the number of citizens is more than the number of werewolves.

\begin{minipage}{\columnwidth}
\textsc{FindCitizen}$(A[l..r])$
\begin{algorithmic}[1]
\If{$l=r$}
  \State \Return $A[l]$
\EndIf
\State $mid = \lfloor (l + r) / 2 \rfloor$
\State $x = \textsc{FindCitizen}(A[l..mid])$
\If{\textsc{IsCitizen}$(A[l..r], x)$}
  \State \Return $x$
\Else
  \State \Return \textsc{FindCitizen}$(A[mid+1..r])$
\EndIf
\end{algorithmic}
\end{minipage}\\[2ex]
The initial call is \textsc{FindCitizen}$([1,2,\ldots,n])$. Correctness: we induce on $r-l$.
\begin{description}
\item[Base case:] If $l=r$, $l$ is the only player. If there are more citizens than werewolves, $A[l]$ must be a citizen.
\item[Induction step:] Assume the algorithm works for all $r-l < k$. Now consider $r-l=k$. We divide it into two halves. Assume \textsc{FindCitizen}$(A[l..mid])$ returns a $x$. If $x$ is a citizen, the algorithm returns $x$ and is correct. If $x$ is a werewolf, then by the induction hypothesis, there left half has no citizens more than werewolves. So the right half must have more citizens than werewolves. The algorithm returns \textsc{FindCitizen}$(A[mid+1..r])$. By the induction hypothesis, it returns a citizen. The algorithm is correct.
\end{description}
Analysis for the running time $T(k), k=r-l+1$: in the worst case, we call \textsc{FindCitizen} twice on size $k/2$ and call \textsc{IsCitizen} once. So $T(k) \le 2T(k/2) + O(k)$. $T(n) = O(n \log n)$.
\item[{(c) [bonus]}] If the number of players is odd, we pick an player $x$ and check its identity. If $x$ is a citizen, we done. Otherwise, we remove $x$ and the number of players is even. If the number of players is even, we pair up the players. For each pair, we query them about each other. We keep one person from the pairs saying each other are citizens and remove the others. Repeat until only one player remains or find a citizen.

\begin{minipage}{\columnwidth}
// Initial call: \textsc{FindCitizenLinear}$([1, 2, \ldots, n])$\\[0.5ex]
\textsc{FindCitizenLinear}$(A[1..k])$
\begin{algorithmic}[1]
\If{$k$ is odd}
  \State $x = A[k]$
  \If{\textsc{IsCitizen}$(A, x)$}
    \State \Return $x$
  \Else
    \State $A=A[1..k-1]$
  \EndIf
\EndIf
\For{$i=1$ to $k/2$}
  \State Query $A[2i-1]$ and $A[2i]$ about each other
  \If{both say the other is citizen}
    \State $B.append(A[2i-1])$
  \EndIf
\EndFor
\State \Return \textsc{FindCitizenLinear}$(B)$
\end{algorithmic}
\end{minipage}\\[2ex]
Correctness: When $k=1$, the algorithm always return $A[1]$ at line 4.
When $k>1$, assume the algorithm is correct for all $k'<k$. If $k$ is odd:
\begin{itemize}
\item If $A[k]$ is a citizen, the algorithm returns $x$ and is correct.
\item If $A[k]$ is a werewolf, the number of citizens in $A[1..k-1]$ is more than the number of werewolves. By the induction hypothesis, the algorithm is correct.
\end{itemize}
If $k$ is even.
The table below shows all possible outcomes of a pair of players:
\begin{center}
\begin{tabular}{c|c|c|c}
Player 1 & Player 2 & Both say citizens? & Keep\\
\hline
Citizen & Citizen & Always & Citizen\\
Citizen & Werewolf & Never & None\\
Werewolf & Citizen & Never & None\\
Werewolf & Werewolf & Maybe & Werewolf\\
\end{tabular}
\end{center}
Assume all the players are divided into 3 groups: $k_1$ pairs of two citizens, $k_2$ pairs of two werewolves, $k_3$ pairs of one citizen and one werewolf.

We have $2k_1 + k_3 > 2k_2 + k_3$. So $k_1 > k_2$. The number of citizens in $B$ is $k_1$ and the number of werewolves is $\le k_2$. There are more citizens than werewolves in $B$. By induction, the algorithm is correct.

The running time $T(k)$: we call \textsc{FindCitizenLinear} once on size at most $k/2$, query $k/2$ pairs of players and the \textsc{IsCitizen}$(k)$ takes O(k) time. So $T(k) \le T(k/2) + O(k)$. $T(n) = O(n)$.
\end{description}

## Problem 5
\begin{description}
\item[(a)] Assume the root is at level 1. The $k$-th ($2\le k\le \lfloor n/2\rfloor$) largest element might at any level from \boxed{2} to \boxed{\min\{k, \lfloor \lg n\rfloor + 1\}} inclusive.
\item[(b)] For min-heap, we can use \textsc{Min-Heapify}$(A, i)$ and \textsc{Heap-Decrease-Key}$(A, i, key)$ to implement \textsc{Hea\nolinebreak pUpdate}$(A, i, val)$.

\begin{minipage}{\columnwidth}
\textsc{HeapUpdate}$(A, i, val)$
\begin{algorithmic}[1]
\If{$A[i] < val$}
  \State $A[i] = val$
  \State \textsc{Min-Heapify}$(A, i)$
\ElsIf{$A[i] > val$}
  \State \textsc{Heap-Decrease-Key}$(A, i, val)$
\EndIf
\end{algorithmic}
\end{minipage}

\begin{minipage}{\columnwidth}
\textsc{Heap-Decrease-Key}$(A, i, key)$
\begin{algorithmic}[1]
\If{$key > A[i]$}
  \State \textbf{error} ``new key is larger than current key''
\EndIf
\State $A[i] = key$
\While{$i > 1$ and $A[\textsc{Parent}(i)] > A[i]$}
  \State swap $A[i]$ and $A[\textsc{Parent}(i)]$
  \State $i = \textsc{Parent}(i)$
\EndWhile
\end{algorithmic}
\end{minipage}

\newcommand{\hy}{\text{-}}
\begin{minipage}{\columnwidth}
\textsc{Min-Heapify}$(A, i)$
\begin{algorithmic}[1]
\State $l = \textsc{Left}(i)$
\State $r = \textsc{Right}(i)$
\If{$l \le A.heap\hy size$ and $A[l] < A[i]$}
  \State $smallest = l$
\Else
  \State $smallest = i$
\EndIf
\If{$r \le A.heap\hy size$ and $A[r] < A[smallest]$}
  \State $smallest = r$
\EndIf
\If{$smallest \ne i$}
  \State swap $A[i]$ and $A[smallest]$
  \State \textsc{Min-Heapify}$(A, smallest)$
\EndIf
\end{algorithmic}
\end{minipage}\\[2ex]
If $A[i] < val$, we increase $A[i]$ to $val$ and call \textsc{Min-Heapify} to maintain the min-heap property in the subtree rooted at $i$. For each node $j$, if
\begin{itemize}
\item $j$ is not in the subtree rooted at $i$. $A[j]$ and $A[\textsc{Parent}(j)]$ are not changed, so $A[j] \ge A[\textsc{Parent}(j)]$ still holds.
\item $j$ is in the subtree rooted at $i$ but $j\neq i$. \textsc{Parent}$(j)$ is also in the subtree. After \textsc{Min-Heapify}, $A[j] \ge A[\textsc{Parent}(j)]$.
\item $j=i$. Assume the elements in the subtree rooted at $i$ before \textsc{HeapUpdate} are $S$.
$A[i]$ is changed from $\min(S)$ to $\min\{S-\{ \min(S) \} + \{ val \}\}$, so it is not decreased.
$A[i] \ge A[\textsc{Parent}(i)]$ holds.
\end{itemize}
If $A[i] > val$, just call \textsc{Heap-Decrease-Key} to maintain the min-heap property.

The \textsc{Min-Heapify} and \textsc{Heap-Decrease-Key} have $O(\log n)$ runtime.
So does \textsc{HeapUpdate}.
\end{description}