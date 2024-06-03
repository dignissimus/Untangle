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
import Untangle.Parsing.Auxiliary
import Untangle.Data.Expression
import Untangle.Data.Diagram
import Untangle.Structure.Monad
import Untangle.Structure.HopfAlgebra
import Untangle.Tactic.Auxiliary

open Lean Meta Server Expr
open ProofWidgets

-- TODO
def parseDeclaration (e : Expr) := do return some (← toString <$> Lean.Meta.ppExpr e, e.getAppFn)

/- -/

def isEquality? (e : Expr) : Option (Expr × Expr) :=
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


open scoped Jsx in
def drawDiagram (language : Diagram.GraphicalLanguage) (side: Side) (components : Diagram.Diagram) (goal : Widget.InteractiveGoal) : IO Html := do
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
      embeds := embeds.push (identifier, read $ diagramLabel Lean.Meta.ppExpr side input)

      if let some previousIdentifier := previous then
        diagramString := diagramString ++ s!"Apply({previousIdentifier}, {identifier})\n"
      previous := some identifier
      currentIdentifiers := currentIdentifiers.append [identifier]

    let mut previousComponent := firstComponent

    let mut row := 0
    for component in components do
      if component.transformation.isIdentity language then
        continue
      previous := none
      previousIdentifiers := currentIdentifiers
      currentIdentifiers := []
      let nextAboveFunctor := s!"X{counter}"
      for output in component.outputs do
        let identifier := s!"X{counter}"
        counter := counter + 1
        currentIdentifiers := currentIdentifiers.append [identifier]
        diagramString := diagramString ++ s!"FunctorLike {identifier}\n"
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
      if component.transformation.isIdentity language then
        for (F, G) in List.zip previousIdentifiers currentIdentifiers do
          diagramString := diagramString ++ s!"WouldTransform({F}, {alpha})\n"
      else
        for index in range component.transformation.left component.transformation.right do
          let F := previousIdentifiers[index]!
          -- Don't draw identity morphisms or identity functors
          if !(component.inputs[index]'sorry).isIdentity language then
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


structure EditDocument where
  edit : Lsp.TextDocumentEdit
  nextLocation : Lsp.Range
deriving RpcEncodable

namespace GraphicalTactic


end GraphicalTactic

namespace String
def lines (s : String) := s.splitOn "\n"
end String


def clickRpc (language : Diagram.GraphicalLanguage) (event : ClickEvent) : RequestM (RequestTask $ Option EditDocument) :=
  RequestM.asTask do
    let (lhs, rhs) := ← match (← do
          event.goal.ctx.val.runMetaM {} do
            let declaration ←  event.goal.mvarId.getDecl
            return isEquality? declaration.type
        ) with
          | some x => return x
          | _ => throw $ .invalidParams s!"Goal is not equality"
    let (diagramL, diagramR) ← event.goal.ctx.val.runMetaM {} do
      let md ← event.goal.mvarId.getDecl
      let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
      Meta.withLCtx lctx md.localInstances do
        return (
          (language.parseExpression lhs).getD (Expression.DebugString "Fail")
          , (language.parseExpression rhs).getD (Expression.DebugString "Fail")
        )


    let diagram := match event.side with
      | .Left => diagramL
      | .Right => diagramR

    let components := (language.renderExpression 1 diagram).getD []

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

    let tacticString' ← language.generateTactic event.goal first second
    if let .none := tacticString' then return fail
    let tacticString := tacticString'.get!

    -- Don't bother using a new line if the current line is empty
    let offset := if isStart then 0 else 1
    let side := event.side

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
def handleClickHopf (params : ClickEvent) : RequestM (RequestTask $ Option EditDocument) := clickRpc hopf params

open Server RequestM in
@[server_rpc_method]
def handleClickMonad (params : ClickEvent) : RequestM (RequestTask $ Option EditDocument) := clickRpc Monad.monad params


@[widget_module]
def UntangleWidget : Component UntangleState where
  javascript := include_str "scripts" / "untangle.js"

open scoped Jsx in
def handleRequest (language : Diagram.GraphicalLanguage) (props : PanelWidgetProps) := RequestM.asTask do
    if let none := props.goals[0]? then
      return <p>No more goals</p>
    let some goal := props.goals[0]? | throw $ .invalidParams "Could not find a goal"
    let goalString := toString goal.type.pretty
    -- throw $ .invalidParams s
    let (lhs, rhs) := ← match (← do
      goal.ctx.val.runMetaM {} do
        let declaration ←  goal.mvarId.getDecl
        return isEquality? declaration.type
    ) with
      | some x => return x
      | _ => throw $ .invalidParams s!"Goal is not equality: {goalString}"

    let (diagLeft, diagRight) ← goal.ctx.val.runMetaM {} do
      let md ← goal.mvarId.getDecl
      let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
      Meta.withLCtx lctx md.localInstances do
        return ((language.parseExpression lhs).getD (Expression.DebugString "Fail"), (language.parseExpression rhs).getD (Expression.DebugString "Fail"))

    let leftComponents := language.renderExpression 1 diagLeft
    let rightComponents := language.renderExpression 1 diagRight

    let componentsL := Option.getD leftComponents []
    let componentsR := Option.getD rightComponents []

    let hidden := Json.mkObj [("display", Json.str "none")]
    return <details «open»={true}>
        <summary className="mv2 pointer">Untangle</summary>
        <div className="ml1">
          {joinDivHorizontal [← drawDiagram language Side.Left componentsL goal, ← drawDiagram language Side.Right componentsR goal]}
          </div>
        <textarea id="serialised-goal" style={hidden}></textarea>
        <UntangleWidget goal={goal} pair={⟨1, 2⟩} position={props.pos}></UntangleWidget>
      </details>

@[server_rpc_method]
def UntangleMonad.rpc := handleRequest Monad.monad

@[server_rpc_method]
def UntangleHopf.rpc := handleRequest hopf

namespace Untangle

@[widget_module]
def UntangleMonad : Component PanelWidgetProps := mk_rpc_widget% UntangleMonad.rpc


@[widget_module]
abbrev Untangle := UntangleMonad


@[widget_module]
def UntangleHopf : Component PanelWidgetProps := mk_rpc_widget% UntangleHopf.rpc
