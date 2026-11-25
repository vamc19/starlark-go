// Copyright 2017 The Bazel Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package resolve_test

import (
	"strings"
	"testing"

	"go.starlark.net/internal/chunkedfile"
	"go.starlark.net/resolve"
	"go.starlark.net/starlarktest"
	"go.starlark.net/syntax"
)

// A test may enable non-standard options by containing (e.g.) "option:recursion".
func getOptions(src string) *syntax.FileOptions {
	return &syntax.FileOptions{
		Set:               option(src, "set"),
		While:             option(src, "while"),
		TopLevelControl:   option(src, "toplevelcontrol"),
		GlobalReassign:    option(src, "globalreassign"),
		LoadBindsGlobally: option(src, "loadbindsglobally"),
		Recursion:         option(src, "recursion"),
		TypeAnnotations:   option(src, "typeannotations"),
	}
}

func option(chunk, name string) bool {
	return strings.Contains(chunk, "option:"+name)
}

func TestResolve(t *testing.T) {
	filename := starlarktest.DataFile("resolve", "testdata/resolve.star")
	for _, chunk := range chunkedfile.Read(filename, t) {
		// A chunk may set options by containing e.g. "option:recursion".
		opts := getOptions(chunk.Source)

		f, err := opts.Parse(filename, chunk.Source, 0)
		if err != nil {
			t.Error(err)
			continue
		}

		if err := resolve.File(f, isPredeclared, isUniversal); err != nil {
			for _, err := range err.(resolve.ErrorList) {
				chunk.GotError(int(err.Pos.Line), err.Msg)
			}
		}
		chunk.Done()
	}
}

func TestDefVarargsAndKwargsSet(t *testing.T) {
	source := "def f(*args, **kwargs): pass\n"
	file, err := syntax.Parse("foo.star", source, 0)
	if err != nil {
		t.Fatal(err)
	}
	if err := resolve.File(file, isPredeclared, isUniversal); err != nil {
		t.Fatal(err)
	}
	fn := file.Stmts[0].(*syntax.DefStmt).Function.(*resolve.Function)
	if !fn.HasVarargs {
		t.Error("HasVarargs not set")
	}
	if !fn.HasKwargs {
		t.Error("HasKwargs not set")
	}
}

func TestLambdaVarargsAndKwargsSet(t *testing.T) {
	source := "f = lambda *args, **kwargs: 0\n"
	file, err := syntax.Parse("foo.star", source, 0)
	if err != nil {
		t.Fatal(err)
	}
	if err := resolve.File(file, isPredeclared, isUniversal); err != nil {
		t.Fatal(err)
	}
	lam := file.Stmts[0].(*syntax.AssignStmt).RHS.(*syntax.LambdaExpr).Function.(*resolve.Function)
	if !lam.HasVarargs {
		t.Error("HasVarargs not set")
	}
	if !lam.HasKwargs {
		t.Error("HasKwargs not set")
	}
}

func isPredeclared(name string) bool { return name == "M" }

func isUniversal(name string) bool {
	switch name {
	case "U", "float", "int", "str", "bool", "list", "dict", "set", "tuple", "None", "True", "False", "type":
		return true
	}
	return false
}

// TestTypeAnnotationsDoNotCapture checks that identifiers that occur
// only in type annotations do not turn locals into cells or create
// free variables.
func TestTypeAnnotationsDoNotCapture(t *testing.T) {
	const src = `
def outer():
    T = float
    def inner(x: T):
        pass
    return inner
`
	opts := &syntax.FileOptions{TypeAnnotations: true}
	f, err := opts.Parse("foo.star", src, 0)
	if err != nil {
		t.Fatal(err)
	}
	if err := resolve.File(f, isPredeclared, isUniversal); err != nil {
		t.Fatal(err)
	}

	outer := f.Stmts[0].(*syntax.DefStmt)
	inner := outer.Body[1].(*syntax.DefStmt)
	outerFn := outer.Function.(*resolve.Function)
	innerFn := inner.Function.(*resolve.Function)

	if len(innerFn.FreeVars) != 0 {
		t.Errorf("annotation created free variables: %v", innerFn.FreeVars)
	}
	for _, bind := range outerFn.Locals {
		if bind.First != nil && bind.First.Name == "T" && bind.Scope != resolve.Local {
			t.Errorf("T has scope %s, want local", bind.Scope)
		}
	}
	typ := inner.Params[0].(*syntax.Ident).Type.(*syntax.Ident)
	if bind, ok := typ.Binding.(*resolve.Binding); !ok || bind.Scope != resolve.Local {
		t.Errorf("annotation T binding = %v, want local", typ.Binding)
	}
}

// TestTypeParamScope checks that type parameters are visible in
// annotations but are not runtime locals.
func TestTypeParamScope(t *testing.T) {
	const src = `
def f[T](x: T) -> T:
    y: T = x
    return y
`
	opts := &syntax.FileOptions{TypeAnnotations: true}
	f, err := opts.Parse("foo.star", src, 0)
	if err != nil {
		t.Fatal(err)
	}
	if err := resolve.File(f, isPredeclared, isUniversal); err != nil {
		t.Fatal(err)
	}

	def := f.Stmts[0].(*syntax.DefStmt)
	fn := def.Function.(*resolve.Function)
	if len(def.TypeParams) != 1 {
		t.Fatalf("got %d type params, want 1", len(def.TypeParams))
	}
	if bind, ok := def.TypeParams[0].Binding.(*resolve.Binding); !ok || bind.Scope != resolve.TypeParam {
		t.Errorf("T binding = %v, want type parameter", def.TypeParams[0].Binding)
	}
	if len(fn.Locals) != 2 {
		t.Errorf("got %d locals, want 2 (x and y)", len(fn.Locals))
	}
	for _, bind := range fn.Locals {
		if bind.First != nil && bind.First.Name == "T" {
			t.Errorf("type parameter T is a runtime local")
		}
	}

	body := def.Body[0].(*syntax.AssignStmt)
	typ := body.LHS.(*syntax.Ident).Type.(*syntax.Ident)
	if bind, ok := typ.Binding.(*resolve.Binding); !ok || bind.Scope != resolve.TypeParam {
		t.Errorf("body annotation T binding = %v, want type parameter", typ.Binding)
	}
}

// TestTypeParamIsNotAValue checks that a type parameter is not visible
// as a runtime value.
func TestTypeParamIsNotAValue(t *testing.T) {
	const src = `
def f[T](x: T):
    return T
`
	opts := &syntax.FileOptions{TypeAnnotations: true}
	f, err := opts.Parse("foo.star", src, 0)
	if err != nil {
		t.Fatal(err)
	}
	err = resolve.File(f, isPredeclared, isUniversal)
	if err == nil {
		t.Fatal("resolution succeeded, want undefined: T")
	}
	if got := err.Error(); !strings.Contains(got, "undefined: T") {
		t.Errorf("got error %q, want undefined: T", got)
	}
	if got := err.Error(); strings.Contains(got, "did you mean") {
		t.Errorf("got error %q, want no spellcheck suggestion", got)
	}
}
