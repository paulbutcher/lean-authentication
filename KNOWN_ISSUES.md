# Known issues

Deliberate limitations of the current implementation, with the reasoning behind them.
Each entry names the requirement it falls short of and what would close the gap.

## Internationalised domain names are not accepted (AUTH-4.5.2)

`Domain.parse` accepts ASCII domains only. A domain containing non-ASCII characters (a
U-label, for example `münchen.de`) is rejected with a distinct error rather than being
converted to punycode. Already-encoded A-labels (`xn--mnchen-3ya.de`) are ordinary ASCII
and are accepted, so an address whose domain has been punycoded upstream works today.

AUTH-4.5.2 requires the conversion to happen in the library, so that two addresses
differing only in IDN encoding are the same address. Until an encoder exists, they are
instead one address and one rejection: no address is silently mapped to the wrong account,
which is the failure that would matter.

The reason for the limitation is placement, not difficulty. RFC 3492 punycode is
general-purpose code with no connection to authentication, and AUTH-2.4 and AUTH-17.5 both
require that such code be surveyed against the ecosystem and, where it does not exist,
raised as a question about which library should own it rather than written here. The survey
found no punycode implementation for Lean 4, and the decision on where it belongs is
outstanding.

Consequences while it stands:

- A tenant whose people have non-ASCII email domains cannot use the library.
- The AUTH-16.1 theorem that domain matching is invariant under IDN normalisation holds
  only over the ASCII domains the parser accepts, which makes it a weaker statement than
  the requirement intends.

Closing it is a drop-in: an encoder applied per label in `Domain.parseFolded`, between the
split on separators and the character check that currently rejects the label. Nothing
downstream of the parser needs to change, because everything downstream already works on
normalised labels.
