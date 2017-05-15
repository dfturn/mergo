// Copyright 2013 Dario Castañé. All rights reserved.
// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Based on src/pkg/reflect/deepequal.go from official
// golang's stdlib.

package mergo

import (
	"fmt"
	"reflect"
)

func deepMergeSlices(a, b *reflect.Value, visited map[uintptr]*visit, depth int, overwrite, backwards bool, listKey string, aIgnores []int) (bFounds []int, err error) {
	for ai := 0; ai < a.Len(); ai++ {
		shouldContinue := false
		for _, ignoreIdx := range aIgnores {
			if ai == ignoreIdx {
				shouldContinue = true
				break
			}
		}
		if shouldContinue {
			continue
		}

		listDst := a.Index(ai)
		didMerge := false

		for bi := 0; bi < b.Len(); bi++ {
			listSrc := b.Index(bi)
			if listSrc.Type() != listDst.Type() {
				continue
			}

			var valueSrc reflect.Value
			var valueDst reflect.Value
			switch listDst.Kind() {
			case reflect.Struct:
				valueSrc = listSrc.FieldByName(listKey)
				valueDst = listDst.FieldByName(listKey)
			case reflect.Map:
				val := reflect.ValueOf(listKey)
				valueSrc = listSrc.MapIndex(val)
				valueDst = listDst.MapIndex(val)
			default:
				continue
			}

			if !valueSrc.IsValid() || !valueDst.IsValid() {
				return bFounds, fmt.Errorf("did not find key: performing full slice diff")
			}

			shouldMerge := valueSrc.String() == valueDst.String()

			if shouldMerge {
				bFounds = append(bFounds, bi)
				if backwards {
					err = deepMerge(listSrc, listDst, visited, depth+1, overwrite, listKey)
				} else {
					err = deepMerge(listDst, listSrc, visited, depth+1, overwrite, listKey)
				}
				didMerge = true
				break
			}
		}

		if !didMerge && backwards {
			newB := reflect.Append(*b, listDst)
			b.Set(newB)
		}
	}
	return bFounds, err
}

// Traverses recursively both values, assigning src's fields values to dst.
// The map argument tracks comparisons that have already been seen, which allows
// short circuiting on recursive types.
func deepMerge(dst, src reflect.Value, visited map[uintptr]*visit, depth int, overwrite bool, listKey string) (err error) {
	if !src.IsValid() {
		return
	}
	if dst.CanAddr() {
		addr := dst.UnsafeAddr()
		h := 17 * addr
		seen := visited[h]
		typ := dst.Type()
		for p := seen; p != nil; p = p.next {
			if p.ptr == addr && p.typ == typ {
				return nil
			}
		}
		// Remember, remember...
		visited[h] = &visit{addr, typ, seen}
	}
	switch dst.Kind() {
	case reflect.Struct:
		for i, n := 0, dst.NumField(); i < n; i++ {
			if err = deepMerge(dst.Field(i), src.Field(i), visited, depth+1, overwrite, listKey); err != nil {
				return
			}
		}
	case reflect.Slice:
		var sliceKind reflect.Kind
		if len(listKey) == 0 {
			// Just do default action if we have no key to act on (this could change with the TODO below)
		} else if dst.Len() > 0 {
			sliceKind = dst.Index(0).Kind()
		} else if src.Len() > 0 {
			sliceKind = src.Index(0).Kind()
		}

		diffed := false
		switch sliceKind {
		case reflect.Struct, reflect.Map:
			var ignores []int

			ignores, err := deepMergeSlices(&dst, &src, visited, depth+1, overwrite, false, listKey, ignores)
			if err == nil {
				_, err = deepMergeSlices(&src, &dst, visited, depth+1, overwrite, true, listKey, ignores)
			}

			if err == nil {
				diffed = true
			}
		}

		// TODO: Could potentially merge more types of slices
		if !diffed && dst.CanSet() && !isEmptyValue(src) && (overwrite || isEmptyValue(dst)) {
			dst.Set(src)
		}
	case reflect.Map:
		for _, key := range src.MapKeys() {
			srcElement := src.MapIndex(key)
			if !srcElement.IsValid() {
				continue
			}
			dstElement := dst.MapIndex(key)
			switch srcElement.Kind() {
			case reflect.Chan, reflect.Func, reflect.Map, reflect.Ptr, reflect.Interface, reflect.Slice:
				if srcElement.IsNil() {
					continue
				}
				fallthrough
			default:
				if !srcElement.CanInterface() {
					continue
				}
				switch reflect.TypeOf(srcElement.Interface()).Kind() {
				case reflect.Struct:
					fallthrough
				case reflect.Ptr:
					fallthrough
				case reflect.Map:
					if err = deepMerge(dstElement, srcElement, visited, depth+1, overwrite, listKey); err != nil {
						return
					}
				}
			}
			if !isEmptyValue(srcElement) && (overwrite || (!dstElement.IsValid() || isEmptyValue(dst))) {
				if dst.IsNil() {
					dst.Set(reflect.MakeMap(dst.Type()))
				}
				dst.SetMapIndex(key, srcElement)
			}
		}
	case reflect.Ptr:
		fallthrough
	case reflect.Interface:
		if src.IsNil() {
			break
		} else if dst.IsNil() || overwrite {
			if dst.CanSet() && (overwrite || isEmptyValue(dst)) {
				dst.Set(src)
			}
		} else if err = deepMerge(dst.Elem(), src.Elem(), visited, depth+1, overwrite, listKey); err != nil {
			return
		}
	default:
		if dst.CanSet() && !isEmptyValue(src) && (overwrite || isEmptyValue(dst)) {
			dst.Set(src)
		}
	}
	return
}

// Merge will fill any empty for value type attributes on the dst struct using corresponding
// src attributes if they themselves are not empty. dst and src must be valid same-type structs
// and dst must be a pointer to struct.
// It won't merge unexported (private) fields and will do recursively any exported field.
func Merge(dst, src interface{}, key string) error {
	return merge(dst, src, false, key)
}

// MergeWithOverwrite will do the same as Merge except that non-empty dst attributes will be overriden by
// non-empty src attribute values.
func MergeWithOverwrite(dst, src interface{}, key string) error {
	return merge(dst, src, true, key)
}

func merge(dst, src interface{}, overwrite bool, key string) error {
	var (
		vDst, vSrc reflect.Value
		err        error
	)
	if vDst, vSrc, err = resolveValues(dst, src); err != nil {
		return err
	}
	if vDst.Type() != vSrc.Type() {
		return ErrDifferentArgumentsTypes
	}
	return deepMerge(vDst, vSrc, make(map[uintptr]*visit), 0, overwrite, key)
}
