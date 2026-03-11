module

public meta import ProofWidgets.Component.Basic

public meta section

namespace VCVioWidgets

open Lean Server

structure RevealLocationProps where
  uri : Lsp.DocumentUri
  range : Lsp.Range
  title? : Option String := none
  deriving RpcEncodable

@[widget_module]
def RevealLocation : ProofWidgets.Component RevealLocationProps where
  javascript := "
import * as React from 'react';
import { EditorContext } from '@leanprover/infoview';

export default function(props) {
  const ec = React.useContext(EditorContext);
  const children = React.Children.toArray(props.children || []);
  return React.createElement(
    'span',
    {
      className: 'link pointer dim',
      title: props.title || '',
      onClick: async (event) => {
        event.preventDefault();
        event.stopPropagation();
        if (ec) {
          await ec.revealLocation({ uri: props.uri, range: props.range });
        }
      }
    },
    ...children
  );
}"

end VCVioWidgets
