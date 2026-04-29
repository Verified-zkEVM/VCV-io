module

public meta import ProofWidgets.Component.Basic

public meta section

namespace VCVioWidgets

open Lean Server

structure RevealLocationProps where
  uri : Lsp.DocumentUri
  range : Lsp.Range
  title? : Option String := none
  block : Bool := false
  deriving RpcEncodable

@[widget_module]
def RevealLocation : ProofWidgets.Component RevealLocationProps where
  javascript := "
import * as React from 'react';
import { EditorContext } from '@leanprover/infoview';

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
