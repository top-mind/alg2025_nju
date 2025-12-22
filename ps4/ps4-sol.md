---
title: ALG Problem Set 4
header-includes: |
  \usepackage{ctex}
  \usepackage{amsthm}
  \usepackage{amsmath}
  \usepackage{algorithm}
  \usepackage[noend]{algpseudocode}
  \usepackage{float}
  \usepackage{caption}
  \algrenewcommand\algorithmiccomment[1]{\hfill// #1}
---
## Problem 1
\begin{description}
\item[(a)] 第 $k$ 小元素是删去最小元素后第 $k-1$ 小的元素。最小堆(优先队列)支持快速删除最小元素，因此可以利用最小堆实现如下算法：

\begin{minipage}{\columnwidth}
\textsc{FindKth}$(A, k)$
\begin{algorithmic}
\State \textsc{BuildMinHeap}$(A)$
\State $B = $ new array of size $k$
\For{$i = 1$ \textbf{to} $k$}
    \State $B[i] = $ \textsc{ExtractMin}$(A)$
\EndFor
\State \Return $B$
\end{algorithmic}
\end{minipage}\\[2ex]
由于 \textsc{BuildMinHeap} 需要 $O(n)$ 时间，每次 \textsc{ExtractMin} 需要 $O(\log n)$ 时间，总时间复杂度为 $O(n+k \log n)$。

\item[(b)] 对每个子问题，下表展示了用最大堆和有序数组存储需要的时间复杂度。
\begin{table}[H]
\begin{tabular}{|c|c|c|c|c|}
\hline
子问题 & 最大堆 & 解释 & 有序数组 & 解释 \\
\hline
查询最大 & $\symbfit{O(\mathbf{1})}$ & A[1] & $\symbfit{O(\mathbf{1})}$ & A[n] \\ 
\hline
删除元素$\!^{1}$(成功) & $\symbfit{O(n) + O(\textbf{lg} n)}$ & 遍历堆 + 调整堆 & $\symbfit{O(\textbf{lg} n) + O(n)}$ & 二分查找 + 顺序移动\\
\hline
删除元素(失败) & $O(n)$ & 遍历堆 & $\symbfit{O(\textbf{lg} n)}$ & 二分查找 \\
\hline
建立数据结构 & $\symbfit{O(n)}$ & \textsc{BuildMaxHeap} & $O(n \lg n)$ & 排序 \\
\hline
查询最小 & $O(n)$ & 遍历叶子$\!^2$ & $\symbfit{O(\mathbf{1})}$ & A[1] \\
\hline
\end{tabular}\\[2ex]
1. 删除元素，假设只提供待删除的元素值，不知道其在数据结构中的位置、是否存在。\\
2. 最小元素可能出现在任意叶子上，需要遍历所有 $\lceil n/2\rceil$ 个叶子。
\end{table}
\end{description}

## Bonus Problem [CLRS 3rd 6.4-5]
放弃。\href{https://walkccc.me/CLRS/Chap06/6.4/#64-5-star}{Walkccc 指出 ``This proved to be quite tricky. Heapsort appeared in 1964, but the lower bound was proved by Schaffer and Sedgewick in 1992. It's evil to put this an exercise.''}

## Problem 2
\begin{description}
\item[(a)] \textbf{引理}：\textsc{Unusual} 算法接受一个长度为 $n=2^d, d\ge 1$ 的数组 $A$，满足 $A[1..2^{d-1}]$ 和 $A[2^{d-1}+1..2^d]$ 均为有序数组，算法返回后，$A$ 为有序数组。\\
\textbf{证明}：对 $d$ 归纳。$d=1$ 时，$n=2$，数组有两个元素，经过交换后显然有序。假设 $d \le k$ 时结论成立，考虑 $d=k+1$ 时的情况。此时 $n=2^{k+1}$, 我们考虑从后往前倒推。要使得 $A$ 有序，在 \textsc{Unusual}$(A[(n/4 + 1)..(3n/4)])$ 前，只要：
\begin{itemize}
\item $A[1..n/4], A[n/4+1..n/2], A[n/2+1..3n/4], A[3n/4+1..n]$ 均为有序数组。
\item $A[1..n/4]$ 恰好包含 $A$ 中前 $n/4$ 小的元素，$A[3n/4+1..n]$ 恰好包含 $A$ 中后 $n/4$ 大的元素。
\end{itemize}
要使得上面两条成立，只要在 \textsc{Unusual}(A[1..n/2]); \textsc{Unusual}(A[n/2+1..n]) 前，
\begin{itemize}
\item $A[1..n/4], A[n/4+1..n/2], A[n/2+1..3n/4], A[3n/4+1..n]$ 均为有序数组。
\item $A[1..n/2]$ 中含有 $A$ 中前 $n/4$ 小的元素。
\item $A[n/2+1..n]$ 中含有 $A$ 中后 $n/4$ 大的元素。
\end{itemize}
只要在 for 循环前，即 \textsc{Unusual} 开始时，
\begin{enumerate}
\item $A[1..n/4], A[n/4+1..n/2], A[n/2+1..3n/4], A[3n/4+1..n]$ 均为有序数组。
\item $A[1..n/4]$ 和 $A[n/2+1..3n/4]$ 中含有 $A$ 中前 $n/4$ 小的元素。
\item $A[n/4+1..n/2]$ 和 $A[3n/4+1..n]$ 中含有 $A$ 中后 $n/4$ 大的元素。
\end{enumerate}
根据函数的 precondition，$A[1..n/2]$ 和 $A[n/2+1..n]$ 均为有序数组，因此 (1) 成立。\\
(假设 $A$ 中元素两两不同) 假设 $A$ 中前 $n/4$ 小的元素不全在 $A[1..n/4]$ 和 $A[n/2+1..3n/4]$ 中，则至少有一个元素在 $A[n/4+1..n/2]$ 或 $[3n/4+1,n]$ 中(不妨设在 A[n/4+1..n/2]中，后者同理)，记为 $x$。由于 $A[1..n/2]$ 有序，$x$ 大于等于 $A[n/4]$ 中的所有元素，因此 $x$ 至少是 $A$ 中第 $n/4+1$ 小的元素，与假设矛盾，因此 (2) 成立。类似地可证 (3) 成立。因此在 for 循环前，(1)(2)(3) 均成立。\\
归纳可证，对任意 $d \ge 1$，\textsc{Unusual} 返回后数组均有序。\\[2ex]
\textbf{定理}：\text{Cruel} 算法接受一个长度为 $n=2^d$ 的数组 $A$，返回后，$A$ 为有序数组。\\
\textbf{证明}：对 $d$ 归纳。$d=0$ 时，$n=1$，数组只有一个元素，显然有序。假设 $d \le k$ 时结论成立，考虑 $d=k+1$ 时的情况。此时 $n=2^{k+1}$, \textsc{Cruel} 调用两次自身处理规模为 $2^k$ 的子问题，根据归纳假设，调用后两个子数组均有序。然后调用 \textsc{Unusual} 处理规模为 $2^{k+1}$ 的子问题，根据引理，调用后整个数组有序。因此对任意 $d$，\textsc{Cruel} 返回后数组均有序。\\[2ex]
\textbf{定理}：\textsc{Cruel} 和 \textsc{Unusual} 调用前后数组元素不变。\\
\textbf{证明}：对调用结构归纳。对于 \textsc{Unusual}，基本情况是 $n=2$，交换两个元素不会改变元素集合。然后显然。
对于 \textsc{Cruel}，基本情况是 $n=1$，只有一个元素，显然不变。然后 \textsc{Cruel} 调用两次自身和一次 \textsc{Unusual}，根据归纳假设，调用前后元素均不变，因此结论成立。\\[2ex]
综上所述，\textsc{Cruel} 算法正确。
\item[(b)] 删去 \textsc{Unusual} 的 for 循环，对于输入 [3 4 1 2], 结果为 [3 1 4 2]。算法不正确。
\item[(c)] 交换 \textsc{Unusual} 的最后两行，对于输入 [3 4 1 2], 结果为 [1 3 2 4]。算法不正确。
\item[(d)] \boxed{\Theta(n^{\log_2 3})}\\
设 \textsc{Unusual} 的运行时间为 $U(n)$, 它调用 3 次自身，每次处理规模为 $n/2$ 的子问题，外加 $\Theta(n)$ 时间的交换操作，因此 $U(n) = 3U(n/2) + \Theta(n)$。根据主定理，$U(n) = \Theta(n^{\log_2 3})$。\\
设 \textsc{Cruel} 的运行时间为 $C(n)$, 它调用 2 次 \textsc{Cruel}，每次处理规模为 $n/2$ 的子问题，外加 $U(n)$ 时间调用 \textsc{Unusual}，因此 $C(n) = 2 C(n/2) + \Theta(n^{\log_2 3})$。根据主定理，$C(n) = \Theta(n^{\log_2 3})$。
\end{description}

## Problem 3
\begin{description}
\item[(a)] 用选择排序的方法，每次选择未排序部分的最小元素放到已排序部分的末尾，由于我们不关心未排序部分，
可以把交换替换成翻转。由于选择排序中不会超过 $n-1$ 次交换，因此翻转次数不会超过 $n-1$ 次，即 $O(n)$ 次。
\item[(b)] 不能，至少需要 $\Omega(n)$ 次翻转，才能保证把任意序列调整为有序。\\
$[1..n]$ 的排列有 $n!$ 种，而一次翻转最多产生 $n^2$ 种不同的排列，因此 $k$ 次翻转最多产生 $n^{2k}$ 种不同的排列方式。\\
要能表示所有排列方式，需满足 $n^{2k} \ge n!$，即 $k \ge \frac{\log(n!)}{2\log n}$。根据斯特林公式，$\log(n!) = \Theta(n \log n)$，因此 $k = \Omega(n)$。
\item[(c) {[bonus]}] 我们考虑类似归并排序的算法。将数组递归地对半分，然后两两合并。合并时，假设左子数组为 $A[i..m],$ 右子数组为 $A[m+1..j]$ 有序，我们把左右子数组各分割成 2 部分，左子数组分割点为 $k$，右子数组分割点为 $l$，使得 $A[i..k]$ 和 $A[m+1..l]$ 中的元素恰好是 $A[i..j]$ 中前 $\lfloor (j-i+1)/2\rfloor$ 小的元素。然后翻转 $A[k+1..m]$，再翻转 $A[m+1..l]$，最后翻转 $A[k+1..l]$。令 $mid = \lfloor (i+j)/2\rfloor$。这样 $A[i..mid]$ 和 $A[mid+1..j]$ 各包含 $A[i..j]$ 中前一半小的元素和后一半大的元素。并且 $A[i..k], A[k+1..mid], A[mid+1..l], A[l+1..j]$ 均为有序数组。可以递归地对 $A[i..mid]$ 和 $A[mid+1..j]$ 进行合并。

\begin{minipage}{\columnwidth}
\textsc{Sort}$(A, i, j)$
\begin{algorithmic}
\If{$i \ge j$}
    \State \Return
\EndIf
\State $mid = \lfloor (i+j)/2 \rfloor$
\State \textsc{Sort}$(A, i, mid)$
\State \textsc{Sort}$(A, mid+1, j)$
\State \textsc{Merge}$(A, i, mid, j)$
\end{algorithmic}
\end{minipage}

\begin{minipage}{\columnwidth}
\textsc{Merge}$(A, i, m, j)$
\begin{algorithmic}
\If{$i \ge j$}
    \State \Return
\EndIf
\State $cnt = \lfloor (j-i+1)/2 \rfloor$
\State $k = i, l = m$
\While{$k \le m$ \textbf{and} $l \le j$ \textbf{and} $cnt > 0$}
    \If{$A[k] < A[l]$}
        \State $k = k + 1$
    \Else
        \State $l = l + 1$
    \EndIf
    \State $cnt = cnt - 1$
\EndWhile
\If{$cnt > 0$}
    \If{$k > m$}
        \State $l = l + cnt$
    \Else
        \State $k = k + cnt$
    \EndIf
\EndIf
\State \textsc{Reverse}$(A, k, m)$
\State \textsc{Reverse}$(A, m+1, l)$
\State \textsc{Reverse}$(A, k, l)$
\State $mid = \lfloor (i+j)/2 \rfloor$
\State \textsc{Merge}$(A, i, k, mid)$
\State \textsc{Merge}$(A, mid+1, l, j)$
\end{algorithmic}
\end{minipage}\\[2ex]
合并总长度 $j-i+1=n$ 的数组时，翻转总长度为 O(n)，因此翻转代价满足 $M(n) = 2M(n/2) + O(n)$，解得 $M(n) = O(n \log n)$。\\
排序总长度为 $n$ 的数组时，翻转代价满足 $S(n) = 2S(n/2) + M(n)$，解得 $S(n) = O(n \log^2 n)$。
\end{description}

## Problem 4
用计数排序的思想：
\begin{minipage}{\columnwidth}
\textsc{Sort}$(A)$
\begin{algorithmic}
\State $n = A.length$
\State $count[red] = count[blue] = count[yellow] = 0$
\For{$i = 1$ \textbf{to} $n$}
    \State $count[A[i].second] = count[A[i].second] + 1$
\EndFor
\State $B = $ copy of $A$
\State $pos[red] = 1$
\State $pos[blue] = count[red] + 1$
\State $pos[yellow] = count[red] + count[blue] + 1$
\For{$i = 1$ \textbf{to} $n$}
    \State $color = B[i].second$
    \State $A[pos[color]] = B[i]$
    \State $pos[color] = pos[color] + 1$
\EndFor
\end{algorithmic}
\end{minipage}
统计每种颜色的数量，然后根据颜色的数量确定每种颜色在最终数组中的位置，最后将元素放入正确的位置。
同一种颜色的元素在原数组中的相对顺序不会改变，因此算法是稳定的，同种颜色元素之间数字保持有序。
由于颜色种类是常数，算法的时间复杂度为 $O(n)$。

## Problem 5
由于 h-index 最大为 $n$。用大小为 $n+1$ 的数组 $count$ 统计每个数字出现的次数，$count[i]$ 记录数字 $i, i < n$ 出现的次数，$count[n]$ 记录大于等于 $n$ 的数字出现的次数。然后从后向前累加出现次数，直到累加和大于等于当前数字 $i$，则 $i$ 即为 h-index。
\begin{minipage}{\columnwidth}
\textsc{HIndex}$(A)$
\begin{algorithmic}
\State $n = A.length$
\State $count[0 \ldots n] = 0$
\For{$i = 1$ \textbf{to} $n$}
    \If{$A[i] < n$}
        \State $count[A[i]] = count[A[i]] + 1$
    \Else
        \State $count[n] = count[n] + 1$
    \EndIf
\EndFor
\State $sum = 0$
\For{$i = n$ \textbf{downto} $0$}
    \State $sum = sum + count[i]$
    \If{$sum \ge i$}
        \State \Return $i$
    \EndIf
\EndFor
\end{algorithmic}
\end{minipage}
算法的时间复杂度为 $O(n)$。

## Problem 6
\begin{description}
\item[(b)] 考虑有序数组的合并+去重，即 
\end{description}
```cpp
std::vector<int> merge_and_unique(const std::vector<int>& A, const std::vector<int>& B) {
    std::vector<int> C;
    C.reserve(A.size() + B.size());

    std::merge(A.begin(), A.end(),
               B.begin(), B.end(),
               std::back_inserter(C));
    auto last = std::unique(C.begin(), C.end());

    C.erase(last, C.end());

    return C;
}
```
对应的伪代码如下，假设 A 和 B 均为按升序排列的数组，且 A、B 中均无重复元素：
\begin{minipage}{\columnwidth}
\textsc{MergeAndUnique}(A, B)
\begin{algorithmic}[1]
\State $n = A.length, m = B.length$
\State $C = $ new array of size $n + m$
\State $i = j = k = 1$
\While{$i \le n$ \textbf{and} $j \le m $}
    \If{$A[i] < B[j]$}
        \State $C[k] = A[i]$
        \State $i = i + 1$
    \ElsIf{$A[i] > B[j]$}
        \State $C[k] = B[j]$
        \State $j = j + 1$
    \Else
        \State $C[k] = A[i]$
        \State $i = i + 1, j = j + 1$
    \EndIf
    \State $k = k + 1$
\EndWhile
\While{$i \le n$}
    \State $C[k] = A[i]$
    \State $i = i + 1, k = k + 1$
\EndWhile
\While{$j \le m$}
    \State $C[k] = B[j]$
    \State $j = j + 1, k = k + 1$
\EndWhile
\State \Return $C[1 \ldots k-1]$
\end{algorithmic}
\end{minipage}
由于 A、B 中无重复元素，合并后若有重复元素，则一定会在第 12 行的分支中遇到，此时只需跳过 B[j] 即可。
所以伪代码 \textsc{MergeAndUnique} 和 `merge_and_unique` 的功能等价。
总时间复杂度为 $O(n)$。

\begin{description}
\item[(a)] 不考虑使用哈希。先分别对数组排序，然后使用上述 \textsc{MergeAndUnique} 合并去重。排序各需要 $O(n \log n)$ 时间，合并去重需要 $O(n)$ 时间，总时间复杂度为 $O(n \log n)$。
\end{description}