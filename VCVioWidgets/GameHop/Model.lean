module

public import Lean

public section

namespace VCVioWidgets
namespace GameHop

open Lean

/-- Stable identifier used to connect diagram nodes and edges. -/
abbrev NodeId := String

/-- Source of explanatory text, resolved from literals, declarations, or the current module. -/
inductive TextSource where
  | none
  | text (contents : String)
  | declDoc (declName : Name)
  | moduleDoc (modName? : Option Name := none)
  | anchorDoc
  deriving Inhabited, Repr, BEq, Hashable

/-- Preferred arrangement of the main game sequence and its side edges. -/
inductive LayoutHint where
  | sequence
  | sequenceWithSideEdges
  deriving Inhabited, DecidableEq, Repr, BEq, Hashable

/-- Role of a node in a game-hopping argument. -/
inductive NodeKind where
  | game
  | hybrid
  | endpoint
  | result
  deriving Inhabited, DecidableEq, Repr, BEq, Hashable

/-- Mathematical relationship represented by an edge between games. -/
inductive EdgeKind where
  | step
  | equivalence
  | equality
  | bound
  | consequence
  deriving Inhabited, DecidableEq, Repr, BEq, Hashable

/-- Kind of declaration attached to a diagram element. -/
inductive AnchorKind where
  | defn
  | theorem
  | reduction
  | result
  deriving Inhabited, DecidableEq, Repr, BEq, Hashable

/-- Whether navigation reveals the whole declaration or its selected name. -/
inductive AnchorMode where
  | declaration
  | selection
  deriving Inhabited, DecidableEq, Repr, BEq, Hashable

/-- Reference to a Lean declaration with its diagram role and navigation mode. -/
structure AnchorRef where
  /-- Fully qualified name of the referenced declaration. -/
  declName : Name
  /-- Role of the declaration in the diagram. -/
  kind : AnchorKind
  /-- Source range to reveal when following the reference. -/
  mode : AnchorMode := .declaration
  deriving Inhabited, DecidableEq, Repr, BEq, Hashable

namespace AnchorRef

/-- Reference a game definition using its declaration range. -/
def defn (declName : Name) : AnchorRef :=
  { declName, kind := .defn }

/-- Reference a theorem using its declaration range. -/
def thm (declName : Name) : AnchorRef :=
  { declName, kind := .theorem }

/-- Reference a reduction using its declaration range. -/
def reduction (declName : Name) : AnchorRef :=
  { declName, kind := .reduction }

/-- Reference the concluding result using its declaration range. -/
def result (declName : Name) : AnchorRef :=
  { declName, kind := .result }

/-- Navigate to the declaration name instead of its full source range. -/
def withSelection (anchor : AnchorRef) : AnchorRef :=
  { anchor with mode := .selection }

end AnchorRef

/-- Content to display beside a game, including signatures, source code, and documentation. -/
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

/-- Use the documentation of the containing diagram element's anchor. -/
def fromAnchorDoc : TextSource :=
  .anchorDoc

end TextSource

namespace CodeSnippet

/-- Display a declaration's signature with interactive Lean code rendering. -/
def signature (declName : Name) : CodeSnippet :=
  .declSignature declName

/-- Display the documentation attached to a declaration. -/
def doc (declName : Name) : CodeSnippet :=
  .declDoc declName

/-- Display the source text of a declaration. -/
def source (declName : Name) : CodeSnippet :=
  .declSource declName

end CodeSnippet

/-- A game or result in a diagram, with explanatory text and source references. -/
structure GameNode where
  /-- Identifier used by edges and the diagram's main path. -/
  id : NodeId
  /-- Role of this node in the argument. -/
  kind : NodeKind := .game
  /-- Short title displayed on the node. -/
  title : String
  /-- Explanatory text displayed beneath the title. -/
  summary : TextSource := .fromAnchorDoc
  /-- Declaration reached by navigating from the node. -/
  anchor? : Option AnchorRef := none
  /-- Additional code and documentation displayed with the node. -/
  snippets : Array CodeSnippet := #[]
  deriving Inhabited, Repr

/-- A supplementary justification attached to a game transition. -/
structure GameEdgeNote where
  /-- Short label describing the justification. -/
  label : String
  /-- Additional explanation of the justification. -/
  detail? : Option String := none
  /-- Declaration supporting the justification. -/
  anchor? : Option AnchorRef := none
  deriving Inhabited, Repr

/-- A directed transition between two named diagram nodes. -/
structure GameEdge where
  /-- Identifier of the transition's starting node. -/
  source : NodeId
  /-- Identifier of the transition's destination node. -/
  target : NodeId
  /-- Relationship established by this transition. -/
  kind : EdgeKind := .step
  /-- Short description displayed on the transition. -/
  label : String
  /-- Additional explanation of the transition. -/
  detail? : Option String := none
  /-- Declaration establishing the transition. -/
  anchor? : Option AnchorRef := none
  /-- Supplementary justifications displayed with the transition. -/
  notes : Array GameEdgeNote := #[]
  deriving Inhabited, Repr

/-- A game-hopping argument presented as a main path with supporting nodes and edges. -/
structure GameDiagram where
  /-- Title displayed above the diagram. -/
  title : String
  /-- Optional explanation displayed beneath the title. -/
  subtitle : TextSource := .none
  /-- Preferred arrangement of nodes and side edges. -/
  layout : LayoutHint := .sequence
  /-- Node identifiers in the order of the main argument. -/
  mainPath : Array NodeId
  /-- Games and results available in the diagram. -/
  nodes : Array GameNode
  /-- Transitions and supporting relationships between nodes. -/
  edges : Array GameEdge := #[]
  deriving Inhabited, Repr

namespace GameDiagram

/-- Find a node by its stable identifier. -/
def findNode? (diagram : GameDiagram) (nodeId : NodeId) : Option GameNode :=
  diagram.nodes.find? (·.id == nodeId)

/-- Find the first edge with the given source and target identifiers. -/
def findEdge? (diagram : GameDiagram) (source target : NodeId) : Option GameEdge :=
  diagram.edges.find? fun edge => edge.source == source && edge.target == target

end GameDiagram

end GameHop
end VCVioWidgets
