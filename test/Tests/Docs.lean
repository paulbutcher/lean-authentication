/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
Every `lean` block in the documentation appears in a module under `Tests/Docs` that compiles.

A worked example that has drifted from the library is worse than none, because it is read as the
thing that works. Compiling the examples catches a change to the library; this catches a change to
a guide that its example did not follow. Lines are compared trimmed, so a block may quote a field
or a call from inside a larger definition at whatever indentation reads best.
-/

namespace Tests.Docs

/-- Each `lean` block in a markdown document, as its lines. -/
def leanBlocks (markdown : String) : List (List String) :=
  go (markdown.splitOn "\n") none []
where
  go : List String → Option (List String) → List (List String) → List (List String)
    | [], _, blocks => blocks.reverse
    | line :: rest, none, blocks =>
      go rest (if line.trimAscii.toString == "```lean" then some [] else none) blocks
    | line :: rest, some block, blocks =>
      if line.trimAscii.toString == "```" then go rest none (block.reverse :: blocks)
      else go rest (some (line :: block)) blocks

private def trimmed (lines : List String) : List String :=
  lines.map (·.trimAscii.toString)

private def appearsAt (block : List String) : List String → Bool
  | [] => block.isEmpty
  | line :: rest => block.isPrefixOf (line :: rest) || appearsAt block rest

/-- Whether the block's lines appear in the source, consecutively. -/
def appearsIn (source : String) (block : List String) : Bool :=
  appearsAt (trimmed block) (trimmed (source.splitOn "\n"))

private structure Guide where
  name : String
  markdown : String
  source : String

private def guides : List Guide :=
  [ ⟨"docs/getting-started.md", include_str "../../docs/getting-started.md",
      include_str "Docs/GettingStarted.lean"⟩,
    ⟨"docs/production.md", include_str "../../docs/production.md",
      include_str "Docs/Production.lean"⟩,
    ⟨"docs/signup.md", include_str "../../docs/signup.md", include_str "Docs/Signup.lean"⟩,
    ⟨"docs/invitations.md", include_str "../../docs/invitations.md",
      include_str "Docs/Invitations.lean"⟩,
    ⟨"docs/federated-sign-in.md", include_str "../../docs/federated-sign-in.md",
      include_str "Docs/Federated.lean"⟩,
    ⟨"docs/enforce-sso.md", include_str "../../docs/enforce-sso.md", include_str "Docs/Sso.lean"⟩,
    ⟨"docs/passkeys.md", include_str "../../docs/passkeys.md", include_str "Docs/Passkeys.lean"⟩,
    ⟨"docs/recovery.md", include_str "../../docs/recovery.md", include_str "Docs/Recovery.lean"⟩,
    ⟨"docs/accounts.md", include_str "../../docs/accounts.md", include_str "Docs/Accounts.lean"⟩,
    ⟨"docs/authorisation-server.md", include_str "../../docs/authorisation-server.md",
      include_str "Docs/AuthorisationServer.lean"⟩ ]

/-- A port number in the guide changed and not in its example, which is the drift this exists to
catch, has to be reported. -/
private def driftCaught : Bool :=
  guides.any fun guide =>
    !(leanBlocks (guide.markdown.replace "8080" "8081")).all (appearsIn guide.source)

def checks : List (String × Bool) :=
  ("a guide edited apart from its example is reported", driftCaught) ::
  guides.flatMap fun guide =>
    let blocks := leanBlocks guide.markdown
    (s!"{guide.name} has code to check", !blocks.isEmpty) ::
      (blocks.zipIdx.map fun (block, i) =>
        (s!"{guide.name}: lean block {i + 1} is in its example", appearsIn guide.source block))

end Tests.Docs
