package iterx_test

import (
	"iter"
	"maps"
	"slices"
	"strconv"
	"testing"

	"github.com/heliorosa/iterx"
	"github.com/stretchr/testify/require"
)

var (
	S    = []int{1, 2, 42, 99}
	sSeq = slices.Values(S)
	sSum = 1 + 2 + 42 + 99
	sStr = []string{"1", "2", "42", "99"}
	SMap = map[int]int{0: 1, 1: 2, 2: 42, 3: 99}
	M    = map[int]string{1: "one", 2: "two", 7: "seven"}
	mSeq = maps.All(M)
	MStr = map[string]string{"1": "one", "2": "two", "7": "seven"}
)

func TestCollectSlice(t *testing.T) {
	require.Equal(t, S, iterx.CollectSlice(sSeq, 16))
}

func TestCollectMap(t *testing.T) {
	require.Equal(t, SMap, iterx.CollectMap(maps.All(SMap), 16))
}

func TestMin(t *testing.T) {
	require.Equal(t, 1, iterx.Min(sSeq))
}

func TestMax(t *testing.T) {
	require.Equal(t, 99, iterx.Max(sSeq))
}

func TestFilter(t *testing.T) {
	require.Equal(
		t,
		S[:2],
		slices.Collect(iterx.Filter(sSeq, func(v int) bool { return v < 10 })),
	)
}

func TestFilter2(t *testing.T) {
	require.Equal(
		t,
		M,
		maps.Collect(iterx.Filter2(mSeq, func(k int, v string) bool { return k < 10 })),
	)
}

func TestMap(t *testing.T) {
	require.Equal(
		t,
		sStr,
		slices.Collect(iterx.Map(sSeq, func(v int) string { return strconv.Itoa(v) })),
	)
}

func TestMap2(t *testing.T) {
	require.Equal(
		t,
		MStr,
		maps.Collect(iterx.Map2(mSeq, func(k int, v string) (string, string) { return strconv.Itoa(k), v })),
	)
}

func TestSum(t *testing.T) {
	require.Equal(t, sSum, iterx.Sum(sSeq))
}

func TestConcat(t *testing.T) {
	require.Equal(
		t,
		append(append(make([]int, 0, len(S)*2), S...), S...),
		slices.Collect(iterx.Concat(sSeq, sSeq)),
	)
}

func TestConcat2(t *testing.T) {
	e := maps.Clone(M)
	mapZero := map[int]string{0: "zero"}
	maps.Copy(e, mapZero)
	require.Equal(
		t,
		e,
		maps.Collect(iterx.Concat2(mSeq, maps.All(mapZero))),
	)
}

func TestFind(t *testing.T) {
	v, ok := iterx.Find(sSeq, func(v int) bool { return v == 42 })
	require.True(t, ok)
	require.Equal(t, 42, v)
	_, ok = iterx.Find(sSeq, func(v int) bool { return false })
	require.False(t, ok)
}

func TestFind2(t *testing.T) {
	k, v, ok := iterx.Find2(mSeq, func(k int, v string) bool { return k == 1 && v == "one" })
	require.True(t, ok)
	require.Equal(t, 1, k)
	require.Equal(t, "one", v)
	_, _, ok = iterx.Find2(mSeq, func(_ int, _ string) bool { return false })
	require.False(t, ok)
}

func TestContains(t *testing.T) {
	require.True(t, iterx.Contains(sSeq, 42))
	require.False(t, iterx.Contains(sSeq, 123))
}

func TestContainsKey(t *testing.T) {
	require.True(t, iterx.ContainsKey(mSeq, 1))
	require.False(t, iterx.ContainsKey(mSeq, 42))
}

func TestContainsValue(t *testing.T) {
	require.True(t, iterx.ContainsValue(mSeq, "one"))
	require.False(t, iterx.ContainsValue(mSeq, "hello world"))
}

func TestDrain(t *testing.T) {
	v, ok := iterx.Drain(sSeq)
	require.True(t, ok)
	require.Equal(t, 99, v)
	_, ok = iterx.Drain(slices.Values([]int{}))
	require.False(t, ok)
}

func TestDrain2(t *testing.T) {
	_, _, ok := iterx.Drain2(mSeq)
	require.True(t, ok)
	_, _, ok = iterx.Drain2(maps.All(map[int]string{}))
	require.False(t, ok)
}

func TestEnumerate(t *testing.T) {
	require.Equal(t, SMap, maps.Collect(iterx.Enumerate(sSeq)))
}

func TestDedup(t *testing.T) {
	require.Equal(t, S, slices.Collect(iterx.Dedup(iterx.Concat(sSeq, sSeq))))
}

func iterLen[T any](seq iter.Seq[T]) int {
	r := 0
	for _ = range seq {
		r++
	}
	return r
}

func iterLen2[K, V any](seq iter.Seq2[K, V]) int {
	r := 0
	for _, _ = range seq {
		r++
	}
	return r
}

func TestSkip(t *testing.T) {
	require.Equal(t, len(S)-2, iterLen(iterx.Skip(sSeq, 2)))
}

func TestSkip2(t *testing.T) {
	require.Equal(t, len(M)-2, iterLen2(iterx.Skip2(mSeq, 2)))
}

func TestLimit(t *testing.T) {
	require.Equal(t, 2, iterLen(iterx.Limit(sSeq, 2)))
}

func TestLimit2(t *testing.T) {
	require.Equal(t, 2, iterLen2(iterx.Limit2(mSeq, 2)))
}
