package iterx

import (
	"cmp"
	"iter"
	"slices"

	"golang.org/x/exp/constraints"
)

func Min[T cmp.Ordered](seq iter.Seq[T]) T {
	return Fold(seq, func(a, b T) T { return when(a < b, a, b) })
}

func Max[T cmp.Ordered](seq iter.Seq[T]) T {
	return Fold(seq, func(a, b T) T { return when(a > b, a, b) })
}

func Filter[T any](seq iter.Seq[T], f func(T) bool) iter.Seq[T] {
	return func(yield func(T) bool) {
		for i := range seq {
			if f(i) && !yield(i) {
				return
			}
		}
	}
}

func Filter2[K, V any](seq iter.Seq2[K, V], f func(K, V) bool) iter.Seq2[K, V] {
	return func(yield func(K, V) bool) {
		for k, v := range seq {
			if f(k, v) && !yield(k, v) {
				return
			}
		}
	}
}

func Map[S, D any](seq iter.Seq[S], f func(S) D) iter.Seq[D] {
	return func(yield func(D) bool) {
		for i := range seq {
			if !yield(f(i)) {
				return
			}
		}
	}
}

func Map2[SK, SV, DK, DV any](seq iter.Seq2[SK, SV], f func(k SK, v SV) (DK, DV)) iter.Seq2[DK, DV] {
	return func(yield func(DK, DV) bool) {
		for k, v := range seq {
			if !yield(f(k, v)) {
				return
			}
		}
	}
}

func Reduce[S, R any](seq iter.Seq[S], ac R, f func(R, S) R) R {
	r := ac
	for i := range seq {
		r = f(r, i)
	}
	return r
}

func Reduce2[K, V, R any](seq iter.Seq2[K, V], ac R, f func(ac R, k K, v V) R) R {
	r := ac
	for k, v := range seq {
		r = f(r, k, v)
	}
	return r
}

func CollectSlice[T any](seq iter.Seq[T], sz int) []T {
	r := make([]T, 0, sz)
	return Reduce(seq, r, func(ac []T, v T) []T { return append(ac, v) })
}

func CollectMap[K comparable, V any](seq iter.Seq2[K, V], sz int) map[K]V {
	r := make(map[K]V, sz)
	return Reduce2(seq, r, func(ac map[K]V, k K, v V) map[K]V {
		ac[k] = v
		return ac
	})
}

func Concat[T any](seqs ...iter.Seq[T]) iter.Seq[T] {
	return Flatten(slices.Values(seqs))
}

func Concat2[K, V any](seqs ...iter.Seq2[K, V]) iter.Seq2[K, V] {
	return Flatten2(slices.Values(seqs))
}

func Find[T any](seq iter.Seq[T], f func(T) bool) (r T, ok bool) {
	var z T
	for i := range seq {
		if f(i) {
			return i, true
		}
	}
	return z, false
}

func Find2[K, V any](seq iter.Seq2[K, V], f func(k K, v V) bool) (k K, v V, ok bool) {
	var (
		zk K
		zv V
	)
	for k, v := range seq {
		if f(k, v) {
			return k, v, true
		}
	}
	return zk, zv, false
}

func Contains[T comparable](seq iter.Seq[T], v T) bool {
	_, ok := Find(seq, func(vv T) bool { return v == vv })
	return ok
}

func ContainsKey[K comparable, V any](seq iter.Seq2[K, V], key K) bool {
	_, _, ok := Find2(seq, func(k K, _ V) bool { return k == key })
	return ok
}

func ContainsValue[K any, V comparable](seq iter.Seq2[K, V], val V) bool {
	_, _, ok := Find2(seq, func(_ K, v V) bool { return v == val })
	return ok
}

type Addable interface {
	constraints.Integer | constraints.Float | constraints.Complex | ~string
}

func Sum[T Addable](seq iter.Seq[T]) T {
	var r T
	for i := range seq {
		r += i
	}
	return r
}

func Skip[T any](seq iter.Seq[T], n int) iter.Seq[T] {
	return func(yield func(T) bool) {
		skipped := 0
		for i := range seq {
			if skipped < n {
				skipped++
				continue
			}
			if !yield(i) {
				return
			}
		}
	}
}

func Skip2[K, V any](seq iter.Seq2[K, V], n int) iter.Seq2[K, V] {
	return func(yield func(K, V) bool) {
		skipped := 0
		for k, v := range seq {
			if skipped < n {
				skipped++
				continue
			}
			if !yield(k, v) {
				return
			}
		}
	}
}

func Limit[T any](seq iter.Seq[T], n int) iter.Seq[T] {
	return func(yield func(T) bool) {
		yielded := 0
		for i := range seq {
			if yielded == n || !yield(i) {
				return
			}
			yielded++
		}
	}
}

func Limit2[K, V any](seq iter.Seq2[K, V], n int) iter.Seq2[K, V] {
	return func(yield func(K, V) bool) {
		yielded := 0
		for k, v := range seq {
			if yielded == n || !yield(k, v) {
				return
			}
			yielded++
		}
	}
}

func Enumerate[T any](seq iter.Seq[T]) iter.Seq2[int, T] {
	return func(yield func(int, T) bool) {
		n := 0
		for i := range seq {
			if !yield(n, i) {
				return
			}
			n++
		}
	}
}

func Dedup[T comparable](seq iter.Seq[T]) iter.Seq[T] {
	return func(yield func(T) bool) {
		seen := make(map[T]struct{}, 16)
		for i := range seq {
			if _, ok := seen[i]; !ok {
				if !yield(i) {
					return
				}
				seen[i] = struct{}{}
			}
		}
	}
}

func Drain[T any](seq iter.Seq[T]) (v T, ok bool) {
	for i := range seq {
		v = i
		ok = true
	}
	return v, ok
}

func Drain2[K, V any](seq iter.Seq2[K, V]) (k K, v V, ok bool) {
	for k, v = range seq {
		ok = true
	}
	return
}

func Flatten[T any](seq iter.Seq[iter.Seq[T]]) iter.Seq[T] {
	return func(yield func(T) bool) {
		for s := range seq {
			for i := range s {
				if !yield(i) {
					return
				}
			}
		}
	}
}

func Flatten2[K, V any](seq iter.Seq[iter.Seq2[K, V]]) iter.Seq2[K, V] {
	return func(yield func(K, V) bool) {
		for s := range seq {
			for k, v := range s {
				if !yield(k, v) {
					return
				}
			}
		}
	}
}

func Fold[T any](seq iter.Seq[T], reducer func(T, T) T) T {
	for i := range seq {
		return Reduce(seq, i, reducer)
	}
	var z T
	return z
}

func when[T any](cond bool, vTrue T, vFalse T) T {
	if cond {
		return vTrue
	}
	return vFalse
}
