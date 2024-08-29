package tree_sitter_jabber_test

import (
	"testing"

	tree_sitter "github.com/smacker/go-tree-sitter"
	"github.com/tree-sitter/tree-sitter-jabber"
)

func TestCanLoadGrammar(t *testing.T) {
	language := tree_sitter.NewLanguage(tree_sitter_jabber.Language())
	if language == nil {
		t.Errorf("Error loading Jabber grammar")
	}
}
