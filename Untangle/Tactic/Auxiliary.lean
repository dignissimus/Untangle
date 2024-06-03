import Init.Data.ToString.Basic
import Mathlib.Data.String.Defs
import Untangle.Data.Diagram
import Untangle.Data.Display

namespace String
  def rep (s : String) : ℕ → String
    | 0 => ""
    | n + 1 => s ++ s.rep n
end String

def withIndent (indent : ℕ) (s : String) := s.splitOn "\n" |> List.map (" ".rep indent ++ .) |> List.intersperse "\n" |> String.join

def Conv (ts : List String) :=
  let commands := ts |> List.map (λ s ↦ s.splitOn "\n") |> List.join |> List.map ("\n" ++ " ".rep 2 ++ .) |> String.join;
  "conv => {" ++ commands ++ "\n}"

def Enter (n : ℕ) := s!"enter [{n}]"
def Slice (l r : ℕ) := s!"slice {l} {r}"
def trySimp := (. ++ "\ntry simp only [CategoryTheory.Category.assoc]")

def trySimpWith (args : List String) := (. ++ s!"\ntry simp only [{ args }]")
def Symm := ("← " ++ .)
def Repeat := ("repeat " ++ .)
def Rewrite : List String → String
  | [] => ""
  | [t] => s!"rw [{t}]"
  | ts => "rw [" ++ (ts.map ("\n  " ++ . ++ ",") |> String.join) ++ "\n]"
def MapComp := "CategoryTheory.Functor.map_comp"

def buildTactic (tactics : List String) (side : Side) (location : ℕ) (indent : ℕ) :=
  [
    Enter side.toNat,
    Slice location (location + 1),
  ] ++ tactics |> Conv |> trySimp |> withIndent indent
