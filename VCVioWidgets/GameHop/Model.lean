module

public import Lean

public section

namespace VCVioWidgets
namespace GameHop

open Lean

abbrev NodeId := String

inductive TextSource where
  | none
  | text (contents : String)
  | declDoc (declName : Name)
  | moduleDoc (modName? : Option Name := none)
  | anchorDoc
  deriving Inhabited, Repr, BEq, Hashable

inductive LayoutHint where
  | sequence
  | sequenceWithSideEdges
  deriving Inhabited, DecidableEq, Repr, BEq, Hashable

inductive NodeKind where
  | game
  | hybrid
  | endpoint
  | result
  deriving Inhabited, DecidableEq, Repr, BEq, Hashable

inductive EdgeKind where
  | step
  | equivalence
  | equality
  | bound
  | consequence
  deriving Inhabited, DecidableEq, Repr, BEq, Hashable

inductive AnchorKind where
  | defn
  | theorem
  | reduction
  | result
  deriving Inhabited, DecidableEq, Repr, BEq, Hashable

inductive AnchorMode where
  | declaration
  | selection
  deriving Inhabited, DecidableEq, Repr, BEq, Hashable

structure AnchorRef where
  declName : Name
  kind : AnchorKind
  mode : AnchorMode := .declaration
  deriving Inhabited, DecidableEq, Repr, BEq, Hashable

namespace AnchorRef

def defn (declName : Name) : AnchorRef :=
  { declName, kind := .defn }

def thm (declName : Name) : AnchorRef :=
  { declName, kind := .theorem }

def reduction (declName : Name) : AnchorRef :=
  { declName, kind := .reduction }

def result (declName : Name) : AnchorRef :=
  { declName, kind := .result }

def withSelection (anchor : AnchorRef) : AnchorRef :=
  { anchor with mode := .selection }

end AnchorRef

inductive CodeSnippet where
  | declName (declName : Name)
  | declType (declName : Name)
  | declSignature (declName : Name)
  | declDoc (declName : Name)
  | declSource (declName : Name)
  | moduleDoc (modName? : Option Name := none)
  | text (contents : String) (anchor? : Option AnchorRef := none)
  deriving Inhabited, Repr, BEq, Hashable

namespace TextSource

def fromAnchorDoc : TextSource :=
  .anchorDoc

end TextSource

namespace CodeSnippet

def signature (declName : Name) : CodeSnippet :=
  .declSignature declName

def doc (declName : Name) : CodeSnippet :=
  .declDoc declName

def source (declName : Name) : CodeSnippet :=
  .declSource declName

end CodeSnippet

structure GameNode where
  id : NodeId
  kind : NodeKind := .game
  title : String
  summary : TextSource := .fromAnchorDoc
  anchor? : Option AnchorRef := none
  snippets : Array CodeSnippet := #[]
  deriving Inhabited, Repr

structure GameEdgeNote where
  label : String
  detail? : Option String := none
  anchor? : Option AnchorRef := none
  deriving Inhabited, Repr

structure GameEdge where
  source : NodeId
  target : NodeId
  kind : EdgeKind := .step
  label : String
  detail? : Option String := none
  anchor? : Option AnchorRef := none
  notes : Array GameEdgeNote := #[]
  deriving Inhabited, Repr

structure GameDiagram where
  title : String
  subtitle : TextSource := .none
  layout : LayoutHint := .sequence
  mainPath : Array NodeId
  nodes : Array GameNode
  edges : Array GameEdge := #[]
  deriving Inhabited, Repr

namespace GameDiagram

def findNode? (diagram : GameDiagram) (nodeId : NodeId) : Option GameNode :=
  diagram.nodes.find? (·.id == nodeId)

def findEdge? (diagram : GameDiagram) (source target : NodeId) : Option GameEdge :=
  diagram.edges.find? fun edge => edge.source == source && edge.target == target

end GameDiagram

end GameHop
end VCVioWidgets
