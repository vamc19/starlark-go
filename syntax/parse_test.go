// Copyright 2017 The Bazel Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package syntax_test

import (
	"bufio"
	"bytes"
	"fmt"
	"go/ast"
	"go/build"
	"go/parser"
	"go/token"
	"os"
	"path/filepath"
	"reflect"
	"slices"
	"strings"
	"testing"

	"go.starlark.net/internal/chunkedfile"
	"go.starlark.net/starlarktest"
	"go.starlark.net/syntax"
)

func TestExprParseTrees(t *testing.T) {
	for _, test := range []struct {
		input, want string
	}{
		{`print(1)`,
			`(CallExpr Fn=print Args=(1))`},
		{"print(1)\n",
			`(CallExpr Fn=print Args=(1))`},
		{`x + 1`,
			`(BinaryExpr X=x Op=+ Y=1)`},
		{`[x for x in y]`,
			`(Comprehension Body=x Clauses=((ForClause Vars=x X=y)))`},
		{`[x for x in (a if b else c)]`,
			`(Comprehension Body=x Clauses=((ForClause Vars=x X=(ParenExpr X=(CondExpr Cond=b True=a False=c)))))`},
		{`x[i].f(42)`,
			`(CallExpr Fn=(DotExpr X=(IndexExpr X=x Y=i) Name=f) Args=(42))`},
		{`x.f()`,
			`(CallExpr Fn=(DotExpr X=x Name=f))`},
		{`x+y*z`,
			`(BinaryExpr X=x Op=+ Y=(BinaryExpr X=y Op=* Y=z))`},
		{`x%y-z`,
			`(BinaryExpr X=(BinaryExpr X=x Op=% Y=y) Op=- Y=z)`},
		{`a + b not in c`,
			`(BinaryExpr X=(BinaryExpr X=a Op=+ Y=b) Op=not in Y=c)`},
		{`lambda x, *args, **kwargs: None`,
			`(LambdaExpr Params=(x (UnaryExpr Op=* X=args) (UnaryExpr Op=** X=kwargs)) Body=None)`},
		{`{"one": 1}`,
			`(DictExpr List=((DictEntry Key="one" Value=1)))`},
		{`a[i]`,
			`(IndexExpr X=a Y=i)`},
		{`a[i:]`,
			`(SliceExpr X=a Lo=i)`},
		{`a[:j]`,
			`(SliceExpr X=a Hi=j)`},
		{`a[::]`,
			`(SliceExpr X=a)`},
		{`a[::k]`,
			`(SliceExpr X=a Step=k)`},
		{`[]`,
			`(ListExpr)`},
		{`[1]`,
			`(ListExpr List=(1))`},
		{`[1,]`,
			`(ListExpr List=(1))`},
		{`[1, 2]`,
			`(ListExpr List=(1 2))`},
		{`()`,
			`(TupleExpr)`},
		{`(4,)`,
			`(ParenExpr X=(TupleExpr List=(4)))`},
		{`(4)`,
			`(ParenExpr X=4)`},
		{`(4, 5)`,
			`(ParenExpr X=(TupleExpr List=(4 5)))`},
		{`1, 2, 3`,
			`(TupleExpr List=(1 2 3))`},
		{`1, 2,`,
			`unparenthesized tuple with trailing comma`},
		{`{}`,
			`(DictExpr)`},
		{`{"a": 1}`,
			`(DictExpr List=((DictEntry Key="a" Value=1)))`},
		{`{"a": 1,}`,
			`(DictExpr List=((DictEntry Key="a" Value=1)))`},
		{`{"a": 1, "b": 2}`,
			`(DictExpr List=((DictEntry Key="a" Value=1) (DictEntry Key="b" Value=2)))`},
		{`{x: y for (x, y) in z}`,
			`(Comprehension Curly Body=(DictEntry Key=x Value=y) Clauses=((ForClause Vars=(ParenExpr X=(TupleExpr List=(x y))) X=z)))`},
		{`{x: y for a in b if c}`,
			`(Comprehension Curly Body=(DictEntry Key=x Value=y) Clauses=((ForClause Vars=a X=b) (IfClause Cond=c)))`},
		{`-1 + +2`,
			`(BinaryExpr X=(UnaryExpr Op=- X=1) Op=+ Y=(UnaryExpr Op=+ X=2))`},
		{`"foo" + "bar"`,
			`(BinaryExpr X="foo" Op=+ Y="bar")`},
		{`-1 * 2`, // prec(unary -) > prec(binary *)
			`(BinaryExpr X=(UnaryExpr Op=- X=1) Op=* Y=2)`},
		{`-x[i]`, // prec(unary -) < prec(x[i])
			`(UnaryExpr Op=- X=(IndexExpr X=x Y=i))`},
		{`a | b & c | d`, // prec(|) < prec(&)
			`(BinaryExpr X=(BinaryExpr X=a Op=| Y=(BinaryExpr X=b Op=& Y=c)) Op=| Y=d)`},
		{`a or b and c or d`,
			`(BinaryExpr X=(BinaryExpr X=a Op=or Y=(BinaryExpr X=b Op=and Y=c)) Op=or Y=d)`},
		{`a and b or c and d`,
			`(BinaryExpr X=(BinaryExpr X=a Op=and Y=b) Op=or Y=(BinaryExpr X=c Op=and Y=d))`},
		{`f(1, x=y)`,
			`(CallExpr Fn=f Args=(1 (BinaryExpr X=x Op== Y=y)))`},
		{`f(*args, **kwargs)`,
			`(CallExpr Fn=f Args=((UnaryExpr Op=* X=args) (UnaryExpr Op=** X=kwargs)))`},
		{`lambda *args, *, x=1, **kwargs: 0`,
			`(LambdaExpr Params=((UnaryExpr Op=* X=args) (UnaryExpr Op=*) (BinaryExpr X=x Op== Y=1) (UnaryExpr Op=** X=kwargs)) Body=0)`},
		{`lambda *, a, *b: 0`,
			`(LambdaExpr Params=((UnaryExpr Op=*) a (UnaryExpr Op=* X=b)) Body=0)`},
		{`a if b else c`,
			`(CondExpr Cond=b True=a False=c)`},
		{`a and not b`,
			`(BinaryExpr X=a Op=and Y=(UnaryExpr Op=not X=b))`},
		{`[e for x in y if cond1 if cond2]`,
			`(Comprehension Body=e Clauses=((ForClause Vars=x X=y) (IfClause Cond=cond1) (IfClause Cond=cond2)))`}, // github.com/google/skylark/issues/53
	} {
		e, err := syntax.ParseExpr("foo.star", test.input, 0)
		var got string
		if err != nil {
			got = stripPos(err)
		} else {
			got = treeString(e)
		}
		if test.want != got {
			t.Errorf("parse `%s` = %s, want %s", test.input, got, test.want)
		}
	}
}

func TestStmtParseTrees(t *testing.T) {
	for _, test := range []struct {
		input, want string
	}{
		{`print(1)`,
			`(ExprStmt X=(CallExpr Fn=print Args=(1)))`},
		{`return 1, 2`,
			`(ReturnStmt Result=(TupleExpr List=(1 2)))`},
		{`return`,
			`(ReturnStmt)`},
		{`for i in "abc": break`,
			`(ForStmt Vars=i X="abc" Body=((BranchStmt Token=break)))`},
		{`for i in "abc": continue`,
			`(ForStmt Vars=i X="abc" Body=((BranchStmt Token=continue)))`},
		{`for x, y in z: pass`,
			`(ForStmt Vars=(TupleExpr List=(x y)) X=z Body=((BranchStmt Token=pass)))`},
		{`if True: pass`,
			`(IfStmt Cond=True True=((BranchStmt Token=pass)))`},
		{`if True: break`,
			`(IfStmt Cond=True True=((BranchStmt Token=break)))`},
		{`if True: continue`,
			`(IfStmt Cond=True True=((BranchStmt Token=continue)))`},
		{`if True: pass
else:
	pass`,
			`(IfStmt Cond=True True=((BranchStmt Token=pass)) False=((BranchStmt Token=pass)))`},
		{"if a: pass\nelif b: pass\nelse: pass",
			`(IfStmt Cond=a True=((BranchStmt Token=pass)) False=((IfStmt Cond=b True=((BranchStmt Token=pass)) False=((BranchStmt Token=pass)))))`},
		{`x, y = 1, 2`,
			`(AssignStmt Op== LHS=(TupleExpr List=(x y)) RHS=(TupleExpr List=(1 2)))`},
		{`x[i] = 1`,
			`(AssignStmt Op== LHS=(IndexExpr X=x Y=i) RHS=1)`},
		{`x.f = 1`,
			`(AssignStmt Op== LHS=(DotExpr X=x Name=f) RHS=1)`},
		{`(x, y) = 1`,
			`(AssignStmt Op== LHS=(ParenExpr X=(TupleExpr List=(x y))) RHS=1)`},
		{`load("", "a", b="c")`,
			`(LoadStmt Module="" From=(a c) To=(a b))`},
		{`if True: load("", "a", b="c")`, // load needn't be at toplevel
			`(IfStmt Cond=True True=((LoadStmt Module="" From=(a c) To=(a b))))`},
		{`def f(x, *args, **kwargs):
	pass`,
			`(DefStmt Name=f Params=(x (UnaryExpr Op=* X=args) (UnaryExpr Op=** X=kwargs)) Body=((BranchStmt Token=pass)))`},
		{`def f(**kwargs, *args): pass`,
			`(DefStmt Name=f Params=((UnaryExpr Op=** X=kwargs) (UnaryExpr Op=* X=args)) Body=((BranchStmt Token=pass)))`},
		{`def f(a, b, c=d): pass`,
			`(DefStmt Name=f Params=(a b (BinaryExpr X=c Op== Y=d)) Body=((BranchStmt Token=pass)))`},
		{`def f(a, b=c, d): pass`,
			`(DefStmt Name=f Params=(a (BinaryExpr X=b Op== Y=c) d) Body=((BranchStmt Token=pass)))`}, // TODO(adonovan): fix this
		{`def f():
	def g():
		pass
	pass
def h():
	pass`,
			`(DefStmt Name=f Body=((DefStmt Name=g Body=((BranchStmt Token=pass))) (BranchStmt Token=pass)))`},
		{"f();g()",
			`(ExprStmt X=(CallExpr Fn=f))`},
		{"f();",
			`(ExprStmt X=(CallExpr Fn=f))`},
		{"f();g()\n",
			`(ExprStmt X=(CallExpr Fn=f))`},
		{"f();\n",
			`(ExprStmt X=(CallExpr Fn=f))`},
	} {
		f, err := syntax.Parse("foo.star", test.input, 0)
		if err != nil {
			t.Errorf("parse `%s` failed: %v", test.input, stripPos(err))
			continue
		}
		if got := treeString(f.Stmts[0]); test.want != got {
			t.Errorf("parse `%s` = %s, want %s", test.input, got, test.want)
		}
	}
}

// TestFileParseTrees tests sequences of statements, and particularly
// handling of indentation, newlines, line continuations, and blank lines.
func TestFileParseTrees(t *testing.T) {
	for _, test := range []struct {
		input, want string
	}{
		{`x = 1
print(x)`,
			`(AssignStmt Op== LHS=x RHS=1)
(ExprStmt X=(CallExpr Fn=print Args=(x)))`},
		{"if cond:\n\tpass",
			`(IfStmt Cond=cond True=((BranchStmt Token=pass)))`},
		{"if cond:\n\tpass\nelse:\n\tpass",
			`(IfStmt Cond=cond True=((BranchStmt Token=pass)) False=((BranchStmt Token=pass)))`},
		{`def f():
	pass
pass

pass`,
			`(DefStmt Name=f Body=((BranchStmt Token=pass)))
(BranchStmt Token=pass)
(BranchStmt Token=pass)`},
		{`pass; pass`,
			`(BranchStmt Token=pass)
(BranchStmt Token=pass)`},
		{"pass\npass",
			`(BranchStmt Token=pass)
(BranchStmt Token=pass)`},
		{"pass\n\npass",
			`(BranchStmt Token=pass)
(BranchStmt Token=pass)`},
		{`x = (1 +
2)`,
			`(AssignStmt Op== LHS=x RHS=(ParenExpr X=(BinaryExpr X=1 Op=+ Y=2)))`},
		{`x = 1 \
+ 2`,
			`(AssignStmt Op== LHS=x RHS=(BinaryExpr X=1 Op=+ Y=2))`},
	} {
		f, err := syntax.Parse("foo.star", test.input, 0)
		if err != nil {
			t.Errorf("parse `%s` failed: %v", test.input, stripPos(err))
			continue
		}
		var buf bytes.Buffer
		for i, stmt := range f.Stmts {
			if i > 0 {
				buf.WriteByte('\n')
			}
			writeTree(&buf, reflect.ValueOf(stmt))
		}
		if got := buf.String(); test.want != got {
			t.Errorf("parse `%s` = %s, want %s", test.input, got, test.want)
		}
	}
}

// TestCompoundStmt tests handling of REPL-style compound statements.
func TestCompoundStmt(t *testing.T) {
	for _, test := range []struct {
		input, want string
	}{
		// blank lines
		{"\n",
			``},
		{"   \n",
			``},
		{"# comment\n",
			``},
		// simple statement
		{"1\n",
			`(ExprStmt X=1)`},
		{"print(1)\n",
			`(ExprStmt X=(CallExpr Fn=print Args=(1)))`},
		{"1;2;3;\n",
			`(ExprStmt X=1)(ExprStmt X=2)(ExprStmt X=3)`},
		{"f();g()\n",
			`(ExprStmt X=(CallExpr Fn=f))(ExprStmt X=(CallExpr Fn=g))`},
		{"f();\n",
			`(ExprStmt X=(CallExpr Fn=f))`},
		{"f(\n\n\n\n\n\n\n)\n",
			`(ExprStmt X=(CallExpr Fn=f))`},
		// complex statements
		{"def f():\n  pass\n\n",
			`(DefStmt Name=f Body=((BranchStmt Token=pass)))`},
		{"if cond:\n  pass\n\n",
			`(IfStmt Cond=cond True=((BranchStmt Token=pass)))`},
		// Even as a 1-liner, the following blank line is required.
		{"if cond: pass\n\n",
			`(IfStmt Cond=cond True=((BranchStmt Token=pass)))`},
		// github.com/google/starlark-go/issues/121
		{"a; b; c\n",
			`(ExprStmt X=a)(ExprStmt X=b)(ExprStmt X=c)`},
		{"a; b c\n",
			`invalid syntax`},
	} {

		// Fake readline input from string.
		// The ! suffix, which would cause a parse error,
		// tests that the parser doesn't read more than necessary.
		sc := bufio.NewScanner(strings.NewReader(test.input + "!"))
		readline := func() ([]byte, error) {
			if sc.Scan() {
				return []byte(sc.Text() + "\n"), nil
			}
			return nil, sc.Err()
		}

		var got string
		f, err := syntax.ParseCompoundStmt("foo.star", readline)
		if err != nil {
			got = stripPos(err)
		} else {
			for _, stmt := range f.Stmts {
				got += treeString(stmt)
			}
		}
		if test.want != got {
			t.Errorf("parse `%s` = %s, want %s", test.input, got, test.want)
		}
	}
}

func stripPos(err error) string {
	s := err.Error()
	if i := strings.Index(s, ": "); i >= 0 {
		s = s[i+len(": "):] // strip file:line:col
	}
	return s
}

// treeString prints a syntax node as a parenthesized tree.
// Idents are printed as foo and Literals as "foo" or 42.
// Structs are printed as (type name=value ...).
// Only non-empty fields are shown.
func treeString(n syntax.Node) string {
	var buf bytes.Buffer
	writeTree(&buf, reflect.ValueOf(n))
	return buf.String()
}

func writeTree(out *bytes.Buffer, x reflect.Value) {
	switch x.Kind() {
	case reflect.String, reflect.Int, reflect.Bool:
		fmt.Fprintf(out, "%v", x.Interface())
	case reflect.Pointer, reflect.Interface:
		if elem := x.Elem(); elem.Kind() == 0 {
			out.WriteString("nil")
		} else {
			writeTree(out, elem)
		}
	case reflect.Struct:
		switch v := x.Interface().(type) {
		case syntax.Literal:
			switch v.Token {
			case syntax.STRING:
				fmt.Fprintf(out, "%q", v.Value)
			case syntax.BYTES:
				fmt.Fprintf(out, "b%q", v.Value)
			case syntax.INT:
				fmt.Fprintf(out, "%d", v.Value)
			}
			return
		case syntax.Ident:
			out.WriteString(v.Name)
			return
		}
		fmt.Fprintf(out, "(%s", strings.TrimPrefix(x.Type().String(), "syntax."))
		for i, n := 0, x.NumField(); i < n; i++ {
			f := x.Field(i)
			if f.Type() == reflect.TypeFor[syntax.Position]() {
				continue // skip positions
			}
			name := x.Type().Field(i).Name
			if name == "commentsRef" {
				continue // skip comments fields
			}
			if f.Type() == reflect.TypeFor[syntax.Token]() {
				fmt.Fprintf(out, " %s=%s", name, f.Interface())
				continue
			}

			switch f.Kind() {
			case reflect.Slice:
				if n := f.Len(); n > 0 {
					fmt.Fprintf(out, " %s=(", name)
					for i := range n {
						if i > 0 {
							out.WriteByte(' ')
						}
						writeTree(out, f.Index(i))
					}
					out.WriteByte(')')
				}
				continue
			case reflect.Pointer, reflect.Interface:
				if f.IsNil() {
					continue
				}
			case reflect.Int:
				if f.Int() != 0 {
					fmt.Fprintf(out, " %s=%d", name, f.Int())
				}
				continue
			case reflect.Bool:
				if f.Bool() {
					fmt.Fprintf(out, " %s", name)
				}
				continue
			}
			fmt.Fprintf(out, " %s=", name)
			writeTree(out, f)
		}
		fmt.Fprintf(out, ")")
	default:
		fmt.Fprintf(out, "%T", x.Interface())
	}
}

func TestParseErrors(t *testing.T) {
	filename := starlarktest.DataFile("syntax", "testdata/errors.star")
	for _, chunk := range chunkedfile.Read(filename, t) {
		_, err := syntax.Parse(filename, chunk.Source, 0)
		switch err := err.(type) {
		case nil:
			// ok
		case syntax.Error:
			chunk.GotError(int(err.Pos.Line), err.Msg)
		default:
			t.Error(err)
		}
		chunk.Done()
	}
}

func TestFilePortion(t *testing.T) {
	// Imagine that the Starlark file or expression print(x.f) is extracted
	// from the middle of a file in some hypothetical template language;
	// see https://github.com/google/starlark-go/issues/346. For example:
	// --
	// {{loop x seq}}
	//   {{print(x.f)}}
	// {{end}}
	// --
	fp := syntax.FilePortion{Content: []byte("print(x.f)"), FirstLine: 2, FirstCol: 4}
	file, err := syntax.Parse("foo.template", fp, 0)
	if err != nil {
		t.Fatal(err)
	}
	span := fmt.Sprint(file.Stmts[0].Span())
	want := "foo.template:2:4 foo.template:2:14"
	if span != want {
		t.Errorf("wrong span: got %q, want %q", span, want)
	}
}

func TestDepthLimit(t *testing.T) {
	// Rather than exceed the stack during parsing, deeply nested
	// expressions and statements are rejected by the recursion
	// counters in the scanner and/or parser.
	for _, src := range []string{
		strings.Repeat("(", 1e7), // (rejected in scanner)
		strings.Repeat("not ", 1e7) + "0",
		strings.Repeat("-", 1e7) + "0",
		strings.Repeat("0 if a else ", 1e7) + "0",
		strings.Repeat("lambda: ", 1e7) + "0",
	} {
		t.Run("", func(t *testing.T) {
			t.Logf("%.65s...", src)
			_, err := syntax.Parse("limit.star", src, 0)
			if err == nil {
				t.Errorf("Parse succeeded unexpectedly")
			} else if !strings.Contains(err.Error(), "excessive nesting") {
				t.Errorf("got error %q, want excessive nesting error", err)
			}
		})
	}
}

// dataFile is the same as starlarktest.DataFile.
// We make a copy to avoid a dependency cycle.
var dataFile = func(pkgdir, filename string) string {
	return filepath.Join(build.Default.GOPATH, "src/go.starlark.net", pkgdir, filename)
}

func BenchmarkParse(b *testing.B) {
	filename := dataFile("syntax", "testdata/scan.star")
	b.StopTimer()
	data, err := os.ReadFile(filename)
	if err != nil {
		b.Fatal(err)
	}
	b.StartTimer()

	for i := 0; i < b.N; i++ {
		_, err := syntax.Parse(filename, data, 0)
		if err != nil {
			b.Fatal(err)
		}
	}
}

// TestParserCallGraphCycles extracts a static call graph from every
// function in parse.go then reports any cyclic path starting from
// ParseFile that does not pass through a function that uses the
// enter/leave mechanism to break cycles.
func TestParserCallGraphCycles(t *testing.T) {
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "parse.go", nil, 0)
	if err != nil {
		t.Fatal(err)
	}

	// function is a node in static call graph.
	type function struct {
		name          string
		callees       map[*function]bool
		cyclebreaking bool
	}
	functions := make(map[string]*function)
	node := func(name string) *function {
		fn, ok := functions[name]
		if !ok {
			fn = &function{
				name:    name,
				callees: make(map[*function]bool),
			}
			t.Logf("node %q", name)
			functions[name] = fn
		}
		return fn
	}
	addEdge := func(caller, callee *function) {
		pre := len(caller.callees)
		caller.callees[callee] = true
		if len(caller.callees) > pre {
			t.Logf("edge %q -> %q", caller.name, callee.name)
		}
	}

	// Extract the functions and the static calls between them.
	var current *function // (nil if uninteresting)
	ast.Inspect(file, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.FuncDecl:
			// decl of function or parser method
			current = nil
			name := n.Name.Name
			if n.Recv != nil && len(n.Recv.List) > 0 {
				if star, ok := n.Recv.List[0].Type.(*ast.StarExpr); ok {
					if id, ok := star.X.(*ast.Ident); ok && id.Name == "parser" {
						current = node("parser." + name)
					}
				}
			} else {
				current = node(name)
			}

		case *ast.CallExpr:
			if current != nil {
				// call within function of interest
				switch fun := n.Fun.(type) {
				case *ast.SelectorExpr:
					// method call
					// Assume p.method() is a method of parser.
					// Ignore all other methods.
					if id, ok := fun.X.(*ast.Ident); ok && id.Name == "p" {
						callee := node("parser." + fun.Sel.Name)

						// A call to p.enter indicates a cycle-breaking function.
						if callee.name == "parser.enter" {
							current.cyclebreaking = true
						}

						addEdge(current, callee)
					}

				case *ast.Ident:
					// function call
					// (incl. junk like: int, len, append, panic)
					addEdge(current, node(fun.Name))
				}
			}
		}
		return true
	})

	// Check that no node belongs to an unbroken cycle.
	// by doing a DFS rooted at each node in turn.
	// (We cannot check once for the whole graph as a
	// cycle may be reached through a cycle-breaking
	// node, but that is not sufficient.)
	for _, f := range functions {
		color := make(map[*function]int) // 0=new, 1=on stack, 2=done
		var stack []*function
		var visit func(*function)
		visit = func(f *function) {
			switch color[f] {
			case 0:
				color[f] = 1
				if !f.cyclebreaking {
					stack = append(stack, f) // push
					for callee := range f.callees {
						visit(callee)
					}
					stack = stack[:len(stack)-1] // pop
				}
				color[f] = 2
			case 1:
				t.Errorf("cycle: %v", f.name)
				for _, caller := range slices.Backward(stack) {
					t.Logf("- %v", caller.name)
				}
			}
		}
		visit(f)
	}

}

// typeOptions returns options with type annotation syntax enabled.
func typeOptions() *syntax.FileOptions {
	return &syntax.FileOptions{TypeAnnotations: true}
}

func TestTypeExprParseTrees(t *testing.T) {
	// Type expressions occur only in type positions, so test them
	// through a cast expression and inspect its Type field.
	for _, test := range []struct {
		input, want string
	}{
		{`int`, `int`},
		{`int | None`, `(BinaryExpr X=int Op=| Y=None)`},
		{`list[int]`, `(IndexExpr X=list Y=int)`},
		{`dict[str, int]`, `(IndexExpr X=dict Y=(TupleExpr List=(str int)))`},
		{`Callable[..., bool]`, `(IndexExpr X=Callable Y=(TupleExpr List=((EllipsisExpr) bool)))`},
		{`foo.bar.Baz`, `(DotExpr X=(DotExpr X=foo Name=bar) Name=Baz)`},
		{`(int)`, `(ParenExpr X=int)`},
		{`(int,)`, `(ParenExpr X=(TupleExpr List=(int)))`},
		{`(int, str)`, `(ParenExpr X=(TupleExpr List=(int str)))`},
		{`()`, `(TupleExpr)`},
		{`(int,) | None`, `(BinaryExpr X=(ParenExpr X=(TupleExpr List=(int))) Op=| Y=None)`},
		{`list[[int]]`, `(IndexExpr X=list Y=(ListExpr List=(int)))`},
		{`struct[{"x": str}]`, `(IndexExpr X=struct Y=(DictExpr List=((DictEntry Key="x" Value=str))))`},
		{`Foo[42]`, `(IndexExpr X=Foo Y=42)`},
		{`Foo["x"]`, `(IndexExpr X=Foo Y="x")`},
	} {
		expr, err := typeOptions().ParseExpr("type.star", `cast(`+test.input+`, x)`, 0)
		if err != nil {
			t.Errorf("parse cast(%s, x) failed: %v", test.input, stripPos(err))
			continue
		}
		cast, ok := expr.(*syntax.CastExpr)
		if !ok {
			t.Errorf("parse cast(%s, x) = %T, want *syntax.CastExpr", test.input, expr)
			continue
		}
		if got := treeString(cast.Type); got != test.want {
			t.Errorf("type %s = %s, want %s", test.input, got, test.want)
		}
	}

	// Check cast/isinstance
	for _, test := range []struct {
		input, want string
	}{
		{`cast(int, x)`, `(CastExpr Type=int X=x)`},
		{`cast(int | None, x,)`, `(CastExpr Type=(BinaryExpr X=int Op=| Y=None) X=x)`},
		{`isinstance(x, list | dict | str)`,
			`(IsInstanceExpr X=x Type=(BinaryExpr X=(BinaryExpr X=list Op=| Y=dict) Op=| Y=str))`},
		{`isinstance(x, int,)`, `(IsInstanceExpr X=x Type=int)`},
	} {
		expr, err := typeOptions().ParseExpr("type.star", test.input, 0)
		var got string
		if err != nil {
			got = stripPos(err)
		} else {
			got = treeString(expr)
		}
		if got != test.want {
			t.Errorf("parse %s = %s, want %s", test.input, got, test.want)
		}
	}
}

func TestTypeExprParseErrors(t *testing.T) {
	for _, test := range []struct {
		src, want string
	}{
		{`cast(Foo[], x)`, "type application must have at least one argument"},
		{`cast(Foo[int,], x)`, "trailing comma not allowed in type application"},
		{`cast(list[int][str], x)`, "want ','"},
		{`cast(int)`, "want ','"},
		{`cast(int, x, y)`, "want ')'"},
		{`isinstance(x)`, "want ','"},
		{`isinstance(x, int, y)`, "want ')'"},
	} {
		_, err := typeOptions().ParseExpr("type.star", test.src, 0)
		if err == nil {
			t.Errorf("parse %s succeeded, want error %q", test.src, test.want)
			continue
		}
		if got := stripPos(err); !strings.Contains(got, test.want) {
			t.Errorf("parse %s error = %q, want substring %q", test.src, got, test.want)
		}
	}
}

func TestTypeStmtParseTrees(t *testing.T) {
	for _, test := range []struct {
		input, want string
	}{
		{`x: int = 1`, `(AssignStmt Op== LHS=x RHS=1)`},
		{`x: int | None`, `(VarStmt Name=x)`},
		{`x: int = 1, 2`, `(AssignStmt Op== LHS=x RHS=(TupleExpr List=(1 2)))`},
		{`type Numeric = int | float`,
			`(TypeAliasStmt Name=Numeric Value=(BinaryExpr X=int Op=| Y=float))`},
		{`type OptionalDict[K, V] = dict[K, V] | None`,
			`(TypeAliasStmt Name=OptionalDict TypeParams=(K V) Value=(BinaryExpr X=(IndexExpr X=dict Y=(TupleExpr List=(K V))) Op=| Y=None))`},
		{`def f(x: int, *args: str, **kwargs: bool) -> int: pass`,
			`(DefStmt Name=f Params=(x (UnaryExpr Op=* X=args) (UnaryExpr Op=** X=kwargs)) ReturnType=int Body=((BranchStmt Token=pass)))`},
		{`def f[T](a: list[T]) -> T: return a[0]`,
			`(DefStmt Name=f TypeParams=(T) Params=(a) ReturnType=T Body=((ReturnStmt Result=(IndexExpr X=a Y=0))))`},
		{`def f[T,](a: T): pass`,
			`(DefStmt Name=f TypeParams=(T) Params=(a) Body=((BranchStmt Token=pass)))`},
	} {
		f, err := typeOptions().Parse("type.star", test.input, 0)
		if err != nil {
			t.Errorf("parse %s failed: %v", test.input, stripPos(err))
			continue
		}
		if got := treeString(f.Stmts[0]); got != test.want {
			t.Errorf("parse %s = %s, want %s", test.input, got, test.want)
		}
	}
}

// TestTypeAnnotationFields checks the annotation fields that treeString omits.
func TestTypeAnnotationFields(t *testing.T) {
	f, err := typeOptions().Parse("type.star", `def f(x: int, *args: str, **kwargs: bool) -> int: pass`, 0)
	if err != nil {
		t.Fatal(err)
	}
	def := f.Stmts[0].(*syntax.DefStmt)
	if got := treeString(def.ReturnType); got != "int" {
		t.Errorf("return type = %s, want int", got)
	}
	params := def.Params
	if got := treeString(params[0].(*syntax.Ident).Type); got != "int" {
		t.Errorf("x type = %s, want int", got)
	}
	if got := treeString(params[1].(*syntax.UnaryExpr).X.(*syntax.Ident).Type); got != "str" {
		t.Errorf("*args type = %s, want str", got)
	}
	if got := treeString(params[2].(*syntax.UnaryExpr).X.(*syntax.Ident).Type); got != "bool" {
		t.Errorf("**kwargs type = %s, want bool", got)
	}

	f, err = typeOptions().Parse("type.star", `x: int = 1`, 0)
	if err != nil {
		t.Fatal(err)
	}
	lhs := f.Stmts[0].(*syntax.AssignStmt).LHS.(*syntax.Ident)
	if got := treeString(lhs.Type); got != "int" {
		t.Errorf("typed assignment type = %s, want int", got)
	}

	f, err = typeOptions().Parse("type.star", `x: int | None`, 0)
	if err != nil {
		t.Fatal(err)
	}
	decl := f.Stmts[0].(*syntax.VarStmt)
	if got := treeString(decl.Name.Type); got != `(BinaryExpr X=int Op=| Y=None)` {
		t.Errorf("var statement type = %s, want int | None", got)
	}
}

func TestTypeStmtParseErrors(t *testing.T) {
	for _, test := range []struct {
		input, want string
	}{
		{`def f[](x): pass`, "type parameter list must not be empty"},
		{`x.y: int = 1`, "want newline"},
		{`cast = 1`, "want '('"},
		{`def f(x: int = 1, *, y: str = "a"): pass`, ""}, // valid
	} {
		_, err := typeOptions().Parse("type.star", test.input, 0)
		if test.want == "" {
			if err != nil {
				t.Errorf("parse %s failed: %v", test.input, stripPos(err))
			}
			continue
		}
		if err == nil {
			t.Errorf("parse %s succeeded, want error %q", test.input, test.want)
			continue
		}
		if got := stripPos(err); !strings.Contains(got, test.want) {
			t.Errorf("parse %s error = %q, want substring %q", test.input, got, test.want)
		}
	}
}

// TestTypeSyntaxDisabled verifies that the new syntax is not accepted
// unless FileOptions.TypeAnnotations is set, preserving backward compatibility.
func TestTypeSyntaxDisabled(t *testing.T) {
	opts := &syntax.FileOptions{}

	// cast(...) is an ordinary call expression when type syntax is disabled.
	expr, err := opts.ParseExpr("f.star", `cast(int, x)`, 0)
	if err != nil {
		t.Fatalf("parse cast(int, x): %v", err)
	}
	if _, ok := expr.(*syntax.CallExpr); !ok {
		t.Errorf("cast(int, x) = %T, want *syntax.CallExpr", expr)
	}

	for _, src := range []string{
		`x: int`,
		`x: int = 1`,
		`type X = int`,
		"def f(x: int): pass",
		"def f[T](): pass",
		"def f() -> int: pass",
	} {
		if _, err := opts.Parse("f.star", src, 0); err == nil {
			t.Errorf("parse %s succeeded, want syntax error", src)
		}
	}
}

// TestDefaultParseTreesUnchanged checks a few parse trees that are
// sensitive to the new '->' and '...' tokens.
func TestDefaultParseTreesUnchanged(t *testing.T) {
	for _, test := range []struct {
		input, want string
	}{
		{`x = a - b > c`, `(AssignStmt Op== LHS=x RHS=(BinaryExpr X=(BinaryExpr X=a Op=- Y=b) Op=> Y=c))`},
		{`x = a - -b`, `(AssignStmt Op== LHS=x RHS=(BinaryExpr X=a Op=- Y=(UnaryExpr Op=- X=b)))`},
		{`x = a > -b`, `(AssignStmt Op== LHS=x RHS=(BinaryExpr X=a Op=> Y=(UnaryExpr Op=- X=b)))`},
		{`x = a.b.c`, `(AssignStmt Op== LHS=x RHS=(DotExpr X=(DotExpr X=a Name=b) Name=c))`},
		{`f(a, b=c, *d, **e)`, `(ExprStmt X=(CallExpr Fn=f Args=(a (BinaryExpr X=b Op== Y=c) (UnaryExpr Op=* X=d) (UnaryExpr Op=** X=e))))`},
		{`lambda x, y=1: x`, `(ExprStmt X=(LambdaExpr Params=(x (BinaryExpr X=y Op== Y=1)) Body=x))`},
		{`x[1:2]`, `(ExprStmt X=(SliceExpr X=x Lo=1 Hi=2))`},
	} {
		f, err := new(syntax.FileOptions).Parse("plain.star", test.input, 0)
		if err != nil {
			t.Errorf("parse %s failed: %v", test.input, err)
			continue
		}
		if got := treeString(f.Stmts[0]); got != test.want {
			t.Errorf("parse %s = %s, want %s", test.input, got, test.want)
		}
	}

	// Numeric literals involving periods must still be recognized.
	for _, src := range []string{`x = 1.`, `x = .5`, `x = 1.5e3`, `x = 0.`, `x = 1.5e-3`} {
		if _, err := new(syntax.FileOptions).Parse("plain.star", src, 0); err != nil {
			t.Errorf("parse %s failed: %v", src, err)
		}
	}
}

// TestTypeNamesUsableAsIdentifiers checks that 'type', 'cast', and
// 'isinstance' remain ordinary names when type annotations are disabled.
func TestTypeNamesUsableAsIdentifiers(t *testing.T) {
	for _, src := range []string{
		`type = 1`,
		`type(x)`,
		`def f(type, cast, isinstance): return cast(type, isinstance)`,
		`x.type = cast.type + isinstance.type`,
		`f(cast=1, isinstance=2)`,
		`load("m", "cast", type="isinstance")`,
	} {
		if _, err := new(syntax.FileOptions).Parse("ident.star", src, 0); err != nil {
			t.Errorf("parse %s failed: %v", src, err)
		}
	}
}

// TestTypeIdentifierAlwaysUsable checks that 'type' never becomes a
// reserved word, even when type annotations are enabled.
func TestTypeIdentifierAlwaysUsable(t *testing.T) {
	for _, src := range []string{
		`type = 1`,
		`type(x)`,
		`def f(type): return type`,
		`x.type`,
	} {
		if _, err := typeOptions().Parse("ident.star", src, 0); err != nil {
			t.Errorf("parse %s failed: %v", src, err)
		}
	}
}
