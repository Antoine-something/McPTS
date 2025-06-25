#[global] Declare Scope mcpts_scope.
#[global] Delimit Scope mcpts_scope with mcpts.
#[global] Bind Scope mcpts_scope with Sortclass.

#[global] Declare Custom Entry judg.

Notation "{{ x }}" := x (at level 0, x custom judg at level 99, format "'{{'  x  '}}'").
