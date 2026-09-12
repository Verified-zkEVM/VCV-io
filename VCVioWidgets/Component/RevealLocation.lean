module

public meta import ProofWidgets.Component.Basic

public meta section

namespace VCVioWidgets

open Lean Server

/-- Properties of a clickable widget that reveals a source range in the editor. -/
structure RevealLocationProps where
  /-- URI of the source document to reveal. -/
  uri : Lsp.DocumentUri
  /-- Source range to reveal and select. -/
  range : Lsp.Range
  /-- Optional tooltip shown over the clickable content. -/
  title? : Option String := none
  /-- Render a block container instead of an inline container. -/
  block : Bool := false
  deriving RpcEncodable

/-- Clickable component that reveals its configured source range in the editor. -/
@[widget_module]
def RevealLocation : ProofWidgets.Component RevealLocationProps where
  javascript := "
public import * as React from 'react';
public import { EditorContext } from '@leanprover/infoview';

export default function(props) {
  const ec = React.useContext(EditorContext);
  const children = React.Children.toArray(props.children || []);
  const Tag = props.block ? 'div' : 'span';
  const className = props.block ? 'pointer dim' : 'link pointer dim';
  const style = props.block ? { cursor: 'pointer' } : undefined;
  return React.createElement(
    Tag,
    {
      className,
      style,
      title: props.title || '',
      onClick: async (event) => {
        if (ec) {
          event.preventDefault();
          event.stopPropagation();
          await ec.revealLocation({ uri: props.uri, range: props.range });
        }
      }
    },
    ...children
  );
}"

end VCVioWidgets
