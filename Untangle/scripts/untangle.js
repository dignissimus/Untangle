import * as React from 'react';
import { RpcContext, EditorContext } from '@leanprover/infoview';

const DEBUG_ELEMENT_ID = "debug-textarea";

const initialiseDebug = () => {
    if (document.getElementById(DEBUG_ELEMENT_ID)) return true;
    const textArea = document.createElement("textarea");
    textArea.id = DEBUG_ELEMENT_ID;
    window.document.body.appendChild(textArea);
};

// const debug = (text) => { document.getElementById(DEBUG_ELEMENT_ID).textContent += text + "\n"; };
const debug = () => { };
const debugError = (e) => debug("Erorr: " + JSON.stringify(e));

const writeTacticIntoEditor = (ec) => (response) => {
    debug("completed: " + JSON.stringify(response))
    ec.api.applyEdit({ documentChanges: [response.edit] });
    ec.revealLocation({ uri: response.edit.textDocument.uri, range: response.nextLocation })
};

let i = 0;
let currentEventListener;
let lastTarget;
let side;
let language;

function fn(params) {
    const rs = React.useContext(RpcContext)
    const ec = React.useContext(EditorContext);
    language = params.languageName;
    if (currentEventListener) {
        window.document.removeEventListener("click", currentEventListener);
    };

    currentEventListener = (event) => {
        let currentTarget;
        if (!event.target.hasAttribute("row") || !event.target.hasAttribute("side")) {
            debugError("Not valid element");
            return;
        };

        currentTarget = [parseInt(event.target.getAttribute("row")), parseInt(event.target.getAttribute("column"))];
        if (!lastTarget || event.target.getAttribute("side") != side) {
            lastTarget = currentTarget;
            side = event.target.getAttribute("side");
            return;
        }

        rs.call("handleClick" + event.target.getAttribute("language"), {
            first: lastTarget,
            second: currentTarget,
            position: params.position,
            goal: params.goal,
            side,
        }).then(writeTacticIntoEditor(ec)).catch(debugError);
        lastTarget = null;
        debug("Sent click to server");
    }

    debug(params.pair.toString());
    debug("done: " + params.pair.toString());
    debug("4");
    window.document.addEventListener('click', currentEventListener);
}

export { fn as default }