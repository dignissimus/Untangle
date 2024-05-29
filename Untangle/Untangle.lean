import Lean.Data.HashMap
import Lean.Elab.Tactic
import Lean.Expr
import Lean.Data.Json.FromToJson
import ProofWidgets.Component.Panel.Basic
import ProofWidgets.Component.PenroseDiagram
import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Component.OfRpcMethod
import Mathlib.Init.Data.List.Instances
import Mathlib.Init.Control.Combinators
import Mathlib.Data.String.Defs

open Lean Meta Server Expr
open ProofWidgets

inductive ExpressionType where
  | Functor
  | Morphism
  | NaturalTransformation
  | Category
  | Object

inductive Expression : ExpressionType → Type where
  | Category (expression: Expr) : Expression Category
  | Object (expression: Expr) : Expression ExpressionType.Object
  | Morphism (expression: Expr) (source: Expression ExpressionType.Object) (target: Expression ExpressionType.Object) : Expression ExpressionType.Morphism
  | NaturalTransformation (expression: Expr) (source: Expression ExpressionType.Functor) (target: Expression ExpressionType.Functor) : Expression NaturalTransformation
  | NaturalTransformationComponent (naturalTransformation : Expression ExpressionType.NaturalTransformation) (object : Expression ExpressionType.Object) (source : Expression ExpressionType.Functor) (target : Expression ExpressionType.Functor): Expression ExpressionType.Morphism
  | Functor (expression: Expr) (source: Expression ExpressionType.Object) (target: Expression ExpressionType.Object) : Expression ExpressionType.Functor
  | FunctorComposition (left : Expression ExpressionType.Functor) (right : Expression ExpressionType.Functor) : Expression ExpressionType.Functor
  | MorphismComposition (expression : Expr) (first: Expression ExpressionType.Morphism) (second: Expression ExpressionType.Morphism) : Expression ExpressionType.Morphism
  | LiftObject (functor : Expression ExpressionType.Functor) (object : Expression ExpressionType.Object) : Expression ExpressionType.Object
  | LiftMap (functor : Expression ExpressionType.Functor) (arrow : Expression ExpressionType.Morphism) : Expression ExpressionType.Morphism
  | PlainExpression (expression : Expr) : Expression _
  | DebugExpression (expression : Expr) : Expression _
  | DebugString (s: String) : Expression _
  deriving Repr

namespace Expression
  def countFunctorApplications : Expression ExpressionType.Functor → Nat
    | Functor _ _ _ => 1
    | FunctorComposition left right => left.countFunctorApplications + right.countFunctorApplications
    | _ => unreachable!

  def countObjectLifts : Expression ExpressionType.Object → Nat
    | Object  _ => 0
    | LiftObject _ object => 1 + object.countObjectLifts
    | _ => unreachable!

  def source : Expression ExpressionType.Morphism → Option (Expression ExpressionType.Object)
    | Morphism _ source _ => source
    | MorphismComposition _ f g => f.source
    | _ => unreachable!

  def target : Expression ExpressionType.Morphism → Option (Expression ExpressionType.Object)
    | Morphism _ _ target => target
    | MorphismComposition _ f g => g.target
    | _ => unreachable!


end Expression

instance : ToString (Expression α) := ToString.mk reprStr

-- TODO
def parseDeclaration (e : Expr) := do return some (← toString <$> Lean.Meta.ppExpr e, e.getAppFn)

/- Utilities -/
def withAppAux? (k : Expr → Array Expr → α) : Expr → Array Expr → Nat → Option α
  | app f a, as, i => some $ withAppAux k f (as.set! i a) (i-1)
  | _, _, _ => none

@[inline] def withApp? (e : Expr) (k : Expr → Array Expr → α) : Option α :=
  let dummy := mkSort levelZero
  let nargs := e.getAppNumArgs
  withAppAux? k e (mkArray nargs dummy) (nargs-1)

/-def constName (e : Expr) : Name :=
  e.constName?.getD Name.anonymous-/

def getAppFnArgs? (e : Expr) : Option $ Name × Array Expr :=
  withApp? e λ e a => (constName e, a)
/- -/


def orElse (f g : α → Option β) : α → Option β
  | x => (f x).orElse (λ _ ↦ g x)

infixl:65 " or " => orElse
macro_rules
  | `(fail) => `(do ← none)


def unknown : Expression α := Expression.DebugString "?"
def morphismFromTo : Expression ExpressionType.Morphism → Expression ExpressionType.Object → Expression ExpressionType.Object → Expression ExpressionType.Morphism
  | (Expression.Morphism morphism _ _), X, Y => Expression.Morphism morphism X Y
  | e, _, _ => e


def natTransFromTo : Expression ExpressionType.NaturalTransformation → Expression ExpressionType.Functor → Expression ExpressionType.Functor → Expression ExpressionType.NaturalTransformation
  | (Expression.NaturalTransformation transformation _ _), F, G => Expression.NaturalTransformation transformation F G
  | e, _, _ => e

mutual
  partial def parseHom (e : Expr) : Option (Expr × Expr) :=
    match getAppFnArgs? e with
      | some (`Quiver.Hom, #[_, _, X, Y]) => return (X, Y)
      | _ => fail

  partial def parseMorphismComposition (e: Expr) : Option (Expression ExpressionType.Morphism) := do
    match getAppFnArgs? e with
      | some (`CategoryTheory.CategoryStruct.comp, #[_, _, X, Y, Z, f, g]) =>
        return Expression.MorphismComposition e
          ( morphismFromTo (← parseMorphism f) (←parseObject X) (←parseObject Y ))
          ( morphismFromTo (← parseMorphism g) (← parseObject Y)  (← parseObject Z))
      | _ => fail


  -- TODO: Major
  partial def parseFunctorComposition (e: Expr) : Option (Expression ExpressionType.Functor) := do
    match getAppFnArgs? e with
      | some (`CategoryTheory.Functor.comp, #[_, _, _, _, _, _, F, G]) => Expression.FunctorComposition (← parseFunctor F) (←parseFunctor G)
      | _ => fail

  -- TODO
  partial def parseSingleton (e : Expr) : Option (Expression α) := return Expression.DebugExpression e

  partial def parseExpression (e : Expr) : Option (Expression α) := return Expression.PlainExpression e


  partial def parseIdentityMorphism(e : Expr) : Option (Expression ExpressionType.Morphism) := do
    match getAppFnArgs? e with
      | some (`CategoryTheory.CategoryStruct.id, #[_, _, X]) => Expression.Morphism e (← parseObject X) (← parseObject X)
      | _ => fail

  -- TODO: Parse the source and destination from the type of the morphism
  partial def parseMorphismName (e : Expr) : Option (Expression ExpressionType.Morphism) :=  return Expression.Morphism e unknown unknown
  partial def parseObjectName (e : Expr) : Option (Expression ExpressionType.Object) :=  return Expression.Object e


  -- TODO
  partial def parseFunctorName (expression : Expr) : Option (Expression ExpressionType.Functor) :=
    match getAppFnArgs? expression with
        | some (`CategoryTheory.Functor.toPrefunctor, #[_, _, C, D]) => do return Expression.Functor expression unknown unknown
        | some (`CategoryTheory.Monad.toFunctor, #[_, _, functor]) => do return Expression.Functor expression unknown unknown
        -- TODO maybe
        | e => Expression.Functor expression unknown unknown
        -- `CategoryTheory.Monad.toFunctor

  partial def parseMorphismLift (e : Expr) : Option (Expression ExpressionType.Morphism) :=
    match getAppFnArgs? e with
      | some (`Prefunctor.map, #[_, _, _, _, functor, X, Y, f]) =>
        return Expression.LiftMap
          (← parseFunctor functor)
          (morphismFromTo (← parseMorphism f) (←parseObject X) (← parseObject Y))
      | _ => fail

  partial def parseObjectLift (e : Expr) : Option (Expression ExpressionType.Object) :=
    match getAppFnArgs? e with
      | some (`Prefunctor.obj, #[_, _, _, _, functor, object]) =>
        return Expression.LiftObject
          (← parseFunctor functor)
          (← parseObject object)
      | _ => fail


  partial def parseNaturalTransformationComponent (e : Expr) : Option (Expression ExpressionType.Morphism) :=
    match getAppFnArgs? e with
      | some (`CategoryTheory.NatTrans.app, #[_, _, _, _, F, G, η, X]) =>
        return Expression.NaturalTransformationComponent
          ( natTransFromTo (← parseNaturalTransformation η) (← parseFunctor F) (←parseFunctor G) )
          (← parseObject X)
          (← parseFunctor F)
          (← parseFunctor G)
      | _ => fail

  partial def parseNaturalTransformation  (e : Expr): Option (Expression ExpressionType.NaturalTransformation) := return Expression.NaturalTransformation e unknown unknown
  partial def parseObject : Expr → Option (Expression ExpressionType.Object) :=
    parseObjectLift
    or parseObjectName

  partial def parseFunctor : Expr → Option (Expression ExpressionType.Functor) :=
    parseFunctorComposition
    or parseFunctorName

  partial def parseMorphism : Expr → Option (Expression ExpressionType.Morphism) :=
    parseMorphismLift
    or parseMorphismComposition
    or parseNaturalTransformationComponent
    or parseIdentityMorphism
    or parseMorphismName

  -- partial def parseDiagram : Expr → Option (Expression _) :=
  --   parseFunctorComposition
  --   or parseMorphismComposition -- TODO: Bad name
  --   or parseSingleton
end

namespace Diagram

inductive FunctorLike where
  | Functor (expr : Expr)
  | Object (expr : Expr)
deriving Repr, BEq

namespace FunctorLike
  def isIdentity : FunctorLike → Bool
    | Functor functor => match getAppFnArgs? functor with
      | some (`CategoryTheory.Functor.id, #[C, _]) => true
      | _ => false
    | _ => False
  /- def name : FunctorLike → String
    | Functor name => name
    | Object name => name -/
end FunctorLike

inductive TransformationLike where
  | NaturalTransformation (expr : Expr)
  | Morphism (expr : Expr)
deriving Repr, BEq

namespace TransformationLike
  def expression : TransformationLike → Expr
    | NaturalTransformation expression => expression
    | Morphism expression => expression

def isIdentity (α : TransformationLike) : Bool :=
  match getAppFnArgs? α.expression with
    | some (`CategoryTheory.CategoryStruct.id, #[_, _, _]) => true
    | _ => false
end TransformationLike

structure Transformation where
  label : TransformationLike
  -- Inclusive range
  left : Nat
  right : Nat

  -- How many outputs this transformation has
  numberOfOutputs : Nat

deriving Repr
namespace Transformation
  def range (left : Nat) (right : Nat) :=  List.map Prod.fst ∘ List.enumFrom left $ List.range (right - left + 1)
  def inputs (α : Transformation) := range α.left α.right
  def isIdentity (α : Transformation) := α.label.isIdentity

  def numberOfInputs (α : Transformation) := α.right - α.left + 1
  def outputStart (α : Transformation) := α.left
  def outputEnd (α : Transformation) := α.left + α.numberOfOutputs - 1
  def outputs(α : Transformation) := range α.outputStart α.outputEnd
end Transformation

structure DiagramComponent where
  inputs : List FunctorLike
  transformation: Transformation
  outputs : List FunctorLike
  location : ℕ
  functorApplications : ℕ := 0
deriving Repr

instance : ToString (DiagramComponent) := ToString.mk reprStr

partial def simplifyFunctor (expression : Expr) : Expr :=
    match getAppFnArgs? expression with
        | some (`CategoryTheory.Functor.toPrefunctor, #[_, _, _, _, functor]) => simplifyFunctor functor
        | some (`CategoryTheory.Monad.toFunctor, #[_, _, monad]) => simplifyFunctor $ monad
        -- TODO maybe
        | _ => expression

def raw : Expression α → Expr
  | .Object object => object
  | .Morphism morphism _ _ => morphism
  | .NaturalTransformation transformation _ _ => transformation
  -- | NaturalTransformationComponent (naturalTransformation : Expression ExpressionType.NaturalTransformation) (object : Expression ExpressionType.Object) (source : Expression ExpressionType.Functor) (target : Expression ExpressionType.Functor): Expression ExpressionType.Morphism
  | .Functor functor _ _ => simplifyFunctor functor
  | _ => Expr.const `Eq [.succ .zero]
  -- | FunctorComposition (left : Expression ExpressionType.Functor) (right : Expression ExpressionType.Functor) : Expression ExpressionType.Functor
  -- | MorphismComposition (first: Expression ExpressionType.Morphism) (second: Expression ExpressionType.Morphism) : Expression ExpressionType.Morphism
  -- | LiftObject (functor : Expression ExpressionType.Functor) (object : Expression ExpressionType.Object) : Expression ExpressionType.Object
  -- | LiftMap (functor : Expression ExpressionType.Functor) (arrow : Expression ExpressionType.Morphism) : Expression ExpressionType.Morphism
  -- | PlainExpression (expression : Expr) : Expression _
  -- | DebugExpression (expression : Expr) : Expression _
  -- | DebugString (s: String) : Expression _
namespace DiagramComponent

def expression (d : DiagramComponent) : Expr := d.transformation.label.expression

def swap (d : DiagramComponent) : DiagramComponent := {d with inputs := d.outputs, outputs := d.inputs}

def shiftLeft (d : DiagramComponent) (shift : Nat) : DiagramComponent := {
    d with
      transformation.left := d.transformation.left - shift
      transformation.right := d.transformation.right - shift
}

def shiftRight (d : DiagramComponent) (shift : Nat) : DiagramComponent := {
    d with
      transformation.left := d.transformation.left + shift
      transformation.right := d.transformation.right + shift
}

abbrev shift := shiftRight


-- Major TODO
def applyFunctor (d : DiagramComponent) (functor : Expression ExpressionType.Functor) : DiagramComponent :=
  let fexp := raw functor;
  {
    d with
    inputs := d.inputs ++ [FunctorLike.Functor fexp]
    outputs := d.outputs ++ [FunctorLike.Functor fexp]
    functorApplications := d.functorApplications + 1
}

def isNaturalTransformation : DiagramComponent → Bool
  | {transformation ..} => match transformation.label with
    | .NaturalTransformation _ => True
    | _ => False

end DiagramComponent

abbrev Diagram := List DiagramComponent

-- Note be careful with the following cases
--  μ : (F ⋙ G) ⟶ (F ⋙ G') where μ is not T.map μ'
def expressionAsDiagramInput : Expression α →  List FunctorLike
  | Expression.Object object => [FunctorLike.Object object]
  | Expression.LiftObject functor object => expressionAsDiagramInput object ++ [FunctorLike.Functor (raw functor)]
  | Expression.Functor functor _source _target => [FunctorLike.Functor functor]
  | Expression.FunctorComposition left right => expressionAsDiagramInput left ++ expressionAsDiagramInput right
  | e => panic! s!"As input: {e}"

partial def morphismAsDiagramComponent (location : ℕ) : Expression ExpressionType.Morphism → Option DiagramComponent
  -- I make the assumption that morphisms map from the source category
  -- But this only holds when the expression is normalised
  -- i.e. let f := T.map f'; f ≫ g'
  -- TODO
  | Expression.Morphism expr source target =>
    do
    let outputs := expressionAsDiagramInput target
      return {
      inputs := expressionAsDiagramInput source
      transformation := {
        label := TransformationLike.Morphism expr, -- TODO: Read from expr, take MetaM as parameter
        left := 0,
        right := source.countObjectLifts,
        numberOfOutputs := outputs.length
      }
      location
      outputs := outputs
    }
  -- TODO: Below case
  | Expression.LiftMap functor morphism => do (← morphismAsDiagramComponent location morphism).applyFunctor functor
  -- TODO: Below case
  -- Might require context? If μ : (T ⋙ T)
  | Expression.NaturalTransformationComponent transformation object source target =>
    do
      return {
        inputs := (← expressionAsDiagramInput object) ++ (← expressionAsDiagramInput source)
        transformation := {
          label := TransformationLike.NaturalTransformation (raw transformation) -- Read from expr
          left := 1 + object.countObjectLifts
          right := object.countObjectLifts + source.countFunctorApplications
          numberOfOutputs := target.countFunctorApplications
        }
        location
        outputs := (← expressionAsDiagramInput object) ++ (← expressionAsDiagramInput target)
      }
  -- TODO: Maybe normalise so this doesn't occur. i.e repeat rw [Functor.comp_assoc]
  -- | Expression.MorphismComposition expr f g => return (← morphismAsDiagramComponent $ Expression.Morphism expr (← f.source) (← g.target))
  | e => panic! s!"Unreachable: {e}"

def constructMorphismDiagram (location : ℕ): Expression ExpressionType.Morphism → Option Diagram
  | Expression.MorphismComposition  _ first second => do
    let left ← constructMorphismDiagram location first
    let last ← left.getLast?
    let offset := last.location + 1
    let right ← constructMorphismDiagram offset second
    return left ++ right
  | morphism => do [← morphismAsDiagramComponent location morphism]

end Diagram

inductive Side where
  | Left
  | Right
deriving Repr, RpcEncodable

namespace Side
def toNat : Side → ℕ
  | Left => 1
  | Right => 2
end Side

instance : ToString Side where
  toString : Side → String
    | .Left => "Left"
    | .Right => "Right"

instance : ToJson Side := ToJson.mk (Json.str ∘ toString)

def isCategoricalEquality? (e : Expr) : Option (Expr × Expr) :=
  let removeType := λ (_, lhs, rhs) ↦ (lhs, rhs);
  removeType <$> e.app3? ``Eq

def joinDivHorizontal (ls : List Html) : Html :=
  Html.element "div" #[("style", Json.mkObj [("display", Json.str "flex"), ("justifyContent", Json.str "space-around")])] ls.toArray

def textStyle := Json.mkObj [("color", Json.str "#00003e"), ("text-decoration", "none")]

open scoped Jsx in
def diagramLabel (f : Expr → MetaM γ) [ToString γ] (side : Side) : Diagram.FunctorLike → MetaM Html
  | Diagram.FunctorLike.Functor functor => return <p></p> -- <p side={toString side}>{(← f  functor) |> toString |> .text}</p>
  | Diagram.FunctorLike.Object object => return <p></p> -- <p side={toString side}>{(← f object) |> toString |> .text}</p>

open scoped Jsx in
def transformationLabel (f : Expr → MetaM γ) [ToString γ] (transformation : Diagram.Transformation) (side : Side) (row : ℕ) (column : ℕ) : MetaM Html :=
    return <p><b><a style={textStyle} side={toString side} row={row} column={column} href="#">{(← f transformation.label.expression) |>  toString |> .text}</a></b></p>

def range (left : Nat) (right : Nat) :=  List.map Prod.fst ∘ List.enumFrom left $ List.range (right - left + 1)

namespace String
  def rep (s : String) : ℕ → String
    | 0 => ""
    | n + 1 => s ++ s.rep n
end String

open scoped Jsx in
def drawDiagram (side: Side) (components : Diagram.Diagram) (goal : Widget.InteractiveGoal) : IO Html := do
    let mut diagramString := ""
    let mut counter := 0
    let firstComponent := List.head components (sorry)
    let mut previous := none
    let mut embeds := #[]
    let mut aboveFunctor := s!"X{counter}"
    let mut previousIdentifiers := []
    let mut currentIdentifiers := []


    let read data := goal.ctx.val.runMetaM {} do
      let md ← goal.mvarId.getDecl
      let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
      Meta.withLCtx lctx md.localInstances do
        return (← data)

    for input in firstComponent.inputs do
      let identifier := s!"X{counter}"
      counter := counter + 1
      diagramString := diagramString ++ s!"FunctorLike {identifier}\n"
      -- embeds := embeds.push (identifier, read $ diagramLabel Lean.Meta.ppExpr input)
      embeds := embeds.push (identifier, read $ diagramLabel Lean.Meta.ppExpr side input)

      if let some previousIdentifier := previous then
        diagramString := diagramString ++ s!"Apply({previousIdentifier}, {identifier})\n"
      previous := some identifier
      currentIdentifiers := currentIdentifiers.append [identifier]

    let mut previousComponent := firstComponent

    let mut row := 0
    for component in components do
      previous := none
      previousIdentifiers := currentIdentifiers
      currentIdentifiers := []
      let nextAboveFunctor := s!"X{counter}"
      for output in component.outputs do
        let identifier := s!"X{counter}"
        counter := counter + 1
        currentIdentifiers := currentIdentifiers.append [identifier]
        diagramString := diagramString ++ s!"FunctorLike {identifier}\n"
        -- embeds := embeds.push (identifier, read $ diagramLabel Lean.Meta.ppExpr output)
        embeds := embeds.push (identifier, read $ diagramLabel Lean.Meta.ppExpr side output)
        if let some previousIdentifier := previous then
          diagramString := diagramString ++ s!"Apply({previousIdentifier}, {identifier})\n"
        previous := some identifier
      diagramString := diagramString ++ s!"Next({aboveFunctor}, {nextAboveFunctor}) \n"
      if component.transformation.left > 0 then
        for index in range 0 (component.transformation.left - 1) do
          let F := previousIdentifiers[index]!
          let G := currentIdentifiers[index]!
          diagramString := diagramString ++ s!"Connect({F}, {G}) \n"


      if component.transformation.right + 1 ≤ component.inputs.length - 1 then do
        for index in range (component.transformation.right + 1) (component.inputs.length - 1) do
          let F := previousIdentifiers[index]!
          let G := currentIdentifiers[index - component.transformation.right + component.transformation.outputEnd]!
          diagramString := diagramString ++ s!"Connect({F}, {G}) \n"

      let alpha := s!"X{counter}"
      counter := counter + 1

      embeds := embeds.push (alpha, read $ transformationLabel Lean.Meta.ppExpr component.transformation side row 0)
      row := row + 1
      diagramString := diagramString ++ s!"NaturalTransformationLike {alpha}\n"
      if component.transformation.isIdentity then
        for (F, G) in List.zip previousIdentifiers currentIdentifiers do
          diagramString := diagramString ++ s!"WouldTransform({F}, {alpha})\n"
      else
        for index in range component.transformation.left component.transformation.right do
          let F := previousIdentifiers[index]!
          -- Don't draw identity morphisms or identity functors
          if !(component.inputs[index]'sorry).isIdentity then
            diagramString := diagramString ++ s!"Transform({F}, {alpha})\n"

        for index in component.transformation.outputs do
          let G := currentIdentifiers[index]!
          diagramString := diagramString ++ s!"Out({alpha}, {G}) \n"

      aboveFunctor := nextAboveFunctor

    let prodSeq : String × IO Html → IO (String × Html) := λ pair ↦ do
      let b' ← Prod.snd pair
      return (Prod.fst pair, b')

    let ioSwap {X : Type} : List (IO X) → IO (List X):= Monad.sequence
    let embeds' ← embeds.toList.map prodSeq |> ioSwap

    return <PenroseDiagram
      embeds={embeds' |> List.toArray}
      dsl={include_str "penrose"/"untangle.dsl"}
      sty={include_str "penrose"/"untangle.sty"}
      sub={diagramString ++ "AutoLabel All"} />

structure UntangleState where
  position : Lsp.Position
  goal : Widget.InteractiveGoal
  pair : ℕ × ℕ
  deriving Server.RpcEncodable

-- This will become more complicated when I add more actions to the user interface
structure ClickEvent where
  first : ℕ × ℕ
  second : ℕ × ℕ
  position : Lsp.Position
  goal : Widget.InteractiveGoal
  side : Side
  deriving RpcEncodable


def isMonadMu? (expression : Expr) :=
  match getAppFnArgs? expression with
    | some (`CategoryTheory.Monad.μ, #[_, _, _]) => true
    | _ => false

def isMonadEta? (expression : Expr) :=
  match getAppFnArgs? expression with
    | some (`CategoryTheory.Monad.η, #[_, _, _]) => true
    | _ => false

def withIndent (indent : ℕ) (s : String) := s.splitOn "\n" |> List.map (" ".rep indent ++ .) |> List.intersperse "\n" |> String.join



-- TODO: Remove excessive whitespace
def Conv (ts : List String) :=
  let commands := ts |> List.map (λ s ↦ s.splitOn "\n") |> List.join |> List.map ("\n" ++ " ".rep 2 ++ .) |> String.join;
  "conv => {" ++ commands ++ "\n}"

def Enter (n : ℕ) := s!"enter [{n}]"
def Slice (l r : ℕ) := s!"slice {l} {r}"
def trySimp := (. ++ "\ntry simp only [CategoryTheory.Category.assoc]")
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

structure EditDocument where
  edit : Lsp.TextDocumentEdit
  nextLocation : Lsp.Range
deriving RpcEncodable

namespace GraphicalTactic

def orElse' (f g : X → Y → (RequestM $ Option α)) (x : X) (y : Y) : RequestM $ Option α :=
  do
    if let Option.some _ := (← f x y) then f x y
    else g x y

infixl:65 " or' " => orElse'
macro_rules
  | `(fail) => `(do ← none)


-- TODO: These rules have simple graphical rules which tell us whether or not we can apply them
--  I shouldn't generate tactics that will fail in lean

-- TODO: Be precise and split this into left unit and right unit rewrites

-- TODO: I'll probably want to package these into functions and write a combinator
def monad_unit (first : Diagram.DiagramComponent) (second : Diagram.DiagramComponent) : RequestM $ Option String :=
  do return do
    if isMonadEta? first.expression && isMonadMu? second.expression then
      return (← fail)
    fail

def monad_assoc (first : Diagram.DiagramComponent) (second : Diagram.DiagramComponent) : RequestM $ Option String  :=
  do return do
    if isMonadMu? first.expression && isMonadMu? second.expression then
      return (← fail)
    fail

def naturality  (first : Diagram.DiagramComponent) (second : Diagram.DiagramComponent)  : RequestM $ Option String:=
  do
    let prettyFirst : String ← sorry
    let prettySecond : String ← sorry
    return do
      if first.isNaturalTransformation then
        return (← fail)
      if second.isNaturalTransformation then
        return (← fail)
      fail

def GraphicalTactic :=
  monad_unit
  or' monad_assoc
  or' naturality

-- TODO: Add more rewrite rules
-- TODO: I have access to the Lean Expr so I don't need to build strings
--  I can build tactics as Expr/Syntax and
--   suggest them along the lines of Lean.Meta.Tactic.TryThis.addSuggestion
def generateTactic (goal : Widget.InteractiveGoal) (first : Diagram.DiagramComponent) (second : Diagram.DiagramComponent) : RequestM $ Option (List String) :=
  do
    let (prettyFirst, prettySecond) ← goal.ctx.val.runMetaM {} do
      let md ← goal.mvarId.getDecl
      let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
      Meta.withLCtx lctx md.localInstances do
        return (
          ← toString <$> Lean.Meta.ppExpr first.transformation.label.expression,
          ← toString <$> Lean.Meta.ppExpr second.transformation.label.expression)

    let exp₁ := first.transformation.label.expression
    let exp₂ := second.transformation.label.expression

    let firstIsMonadMu := isMonadMu? exp₁
    let secondIsMonadMu := isMonadMu? exp₂

    let firstIsMonadEta := isMonadEta? exp₁
    let secondIsMonadEta := isMonadEta? exp₂

    -- TODO: Only include the `repeat map_comp` lines when necessary (i.e. check the functor lift count)
    if firstIsMonadEta && secondIsMonadMu then
      let mut tactics := [Repeat $ Rewrite [Symm MapComp]]
      -- TODO: Functor names should be the same
      if first.functorApplications > second.functorApplications then
        tactics := tactics.concat $ Rewrite ["Monad.right_unit"]
      else
        tactics := tactics.concat $ Rewrite ["Monad.left_unit"]
      tactics := tactics.concat $ Repeat (Rewrite [MapComp])
      return tactics
    else if firstIsMonadMu && secondIsMonadMu then
      let mut tactics := [Repeat $ Rewrite [Symm MapComp]]
      if first.functorApplications > second.functorApplications then
        tactics := tactics.concat $ Rewrite ["Monad.assoc"]
      else
        tactics := tactics.concat $ Rewrite ["← Monad.assoc"]
      tactics := tactics.concat $ Repeat (Rewrite [MapComp])
      return tactics
    else if first.isNaturalTransformation then
      return [
        Repeat $ Rewrite [Symm MapComp],
        Rewrite [
          Symm s!"({prettyFirst}).naturality ({prettySecond})",
          "CategoryTheory.Functor.comp_map"
        ],
        Repeat $ Rewrite [MapComp]
      ]
    else if second.isNaturalTransformation then
      return [
        Repeat $ Rewrite [Symm MapComp],
        Rewrite [
          Symm "CategoryTheory.Functor.comp_map",
          s!"({prettySecond}).naturality ({prettyFirst})"
        ],
        Repeat $ Rewrite [MapComp]
      ]
    return .none
end GraphicalTactic

namespace String
def lines (s : String) := s.splitOn "\n"
end String

def clickRpc (event : ClickEvent) : RequestM (RequestTask $ Option EditDocument) :=
  RequestM.asTask do
    let (lhs, rhs) := ← match (← do
          event.goal.ctx.val.runMetaM {} do
            let declaration ←  event.goal.mvarId.getDecl
            return isCategoricalEquality? declaration.type
        ) with
          | some x => return x
          | _ => throw $ .invalidParams s!"Goal is not equality"
    let (diagramL, diagramR) ← event.goal.ctx.val.runMetaM {} do
      let md ← event.goal.mvarId.getDecl
      let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
      Meta.withLCtx lctx md.localInstances do
        return (
          (parseMorphism lhs).getD (Expression.DebugString "Fail")
          , (parseMorphism rhs).getD (Expression.DebugString "Fail")
        )


    let diagram := match event.side with
      | .Left => diagramL
      | .Right => diagramR

    let components := Diagram.constructMorphismDiagram 1 diagram |> Option.getD $ []

    let (firstPair, secondPair) :=
      if event.first.1 < event.second.1
        then (event.first, event.second)
        else (event.second, event.first)

    let (firstRow, firstColumn) := firstPair
    let (secondRow, secondColumn) := secondPair

    let first := components[firstRow]'sorry -- Top expression
    let second := components[secondRow]'sorry -- Bottom expression

    let doc ← RequestM.readDoc

    let fm := doc.meta.text
    let spos := Lean.FileMap.lspPosToUtf8Pos fm event.position
    let lineStart := Lean.findLineStart fm.source spos
    let (indent, isStart) := Lean.findIndentAndIsStart fm.source spos

    -- TODO: I don't want to panic if we can't apply a tactic
    let tacticString' ← GraphicalTactic.generateTactic event.goal first second
    if let .none := tacticString' then return fail
    let tacticString := tacticString'.get!

    -- Don't bother using a new line if the current line is empty
    let offset := if isStart then 0 else 1
    let side := event.side

    -- TODO: second.location = first.location + 1
    let location := first.location
    let command := buildTactic tacticString side location indent
    let position' := ⟨event.position.line + offset, 0⟩
    let position'' := ⟨event.position.line + offset + command.lines.length, indent⟩

    event.goal.ctx.val.runMetaM {} do
      return .some {
        edit := {
        textDocument := {
          uri := doc.meta.uri,
          version? := doc.meta.version
        },
        edits := #[{
          range := Lsp.Range.mk position' position'
          newText := command ++ "\n" ++ " ".rep indent
          }],
        }
        nextLocation := ⟨position'', position''⟩
      }


open Server RequestM in
@[server_rpc_method]
def handleClick (params : ClickEvent) : RequestM (RequestTask $ Option EditDocument) := clickRpc params


@[widget_module]
def UntangleWidget : Component UntangleState where
  javascript := include_str "scripts" / "untangle.js"

-- Probably shouldn't throw
open scoped Jsx in
@[server_rpc_method]
def Untangle.rpc (props : PanelWidgetProps) : RequestM (RequestTask Html) :=
  RequestM.asTask do
    if let none := props.goals[0]? then
      return <p>No more goals</p>
    let some goal := props.goals[0]? | throw $ .invalidParams "Could not find a goal"
    let goalString := toString goal.type.pretty
    -- throw $ .invalidParams s
    let (lhs, rhs) := ← match (← do
      goal.ctx.val.runMetaM {} do
        let declaration ←  goal.mvarId.getDecl
        return isCategoricalEquality? declaration.type
    ) with
      | some x => return x
      | _ => throw $ .invalidParams s!"Goal is not equality: {goalString}"

    let (diagLeft, diagRight) ← goal.ctx.val.runMetaM {} do
      let md ← goal.mvarId.getDecl
      let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
      Meta.withLCtx lctx md.localInstances do
        return ((parseMorphism lhs).getD (Expression.DebugString "Fail"), (parseMorphism rhs).getD (Expression.DebugString "Fail"))

    let leftComponents := Diagram.constructMorphismDiagram 1 diagLeft
    let rightComponents := Diagram.constructMorphismDiagram 1 diagRight

    let componentsL := Option.getD leftComponents []
    let componentsR := Option.getD rightComponents []

    let hidden := Json.mkObj [("display", Json.str "none")]
    return <details «open»={true}>
        <summary className="mv2 pointer">Untangle</summary>
        <div className="ml1">
          {joinDivHorizontal [← drawDiagram Side.Left componentsL goal, ← drawDiagram Side.Right componentsR goal]}
          </div>
        <textarea id="serialised-goal" style={hidden}></textarea>
        <UntangleWidget goal={goal} pair={⟨1, 2⟩} position={props.pos}></UntangleWidget>
      </details>

namespace Untangle

@[widget_module]
def Untangle : Component PanelWidgetProps :=
  mk_rpc_widget% Untangle.rpc
