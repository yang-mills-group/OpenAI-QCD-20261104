import YM.Massive.Reservoir.Norm
import YM.Massive.Reservoir.Pipes

/-! Explicit (& not eventually-quantified) volume threshold for chess estimates.
So applies also at a *moving resolution*. Proof copies arithmetic from
`YM/QCD/Agate/Limbs.lean`. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Agate.Paving
open Plum Land Lattice Wilson Grass Lat NormedSpace Function MeasureTheory Filter RP Kit Finset RG Push.GridApprox Jets
open scoped BigOperators Matrix.Norms.L2Operator Matrix Topology ComplexOrder Classical
variable {n c f : Side}{F:ℕ}{β:ℝ} {R:Cells.Cut c} {K:KernelChoices}
open Tide Flume YM.Next.Free Kites Acre Rails Rain Loom Fleet
variable {X:Pixel c F}{J:Patch}{w z:ℝ} {A:Set (Site c)}
variable {D S Y:Lot}

lemma sail (r:ℕ)(H:D ⊆ Lattice.box r)(hk:2*r<c.val)(p:Site c):windows D p ⊆ RP.square (leap p (fun _=> -(r:ℤ))) (fun _=>2*r+1):=by
   have hr:=H; rintro x ⟨x,hx,rfl⟩ j
   let t:= x j +(r:ℤ); have h:= box_test.mp (hr hx); have h0:=h.1 j; have h1:=h.2 j; have he :t ≤2*r:=by unfold t; omega
   have hp : 0 ≤ t:=by unfold t; omega
   let N:= c; have hv: t.toNat < c.val:=by omega
   change (leap p x j-leap p (fun _=> -(r:ℤ)) j).val <2*r+1; rw [show leap p x j-leap p (fun _=> -(r:ℤ)) j=((t.toNat:ℕ):Per c) from ?_,ZMod.val_natCast_of_lt hv]; omega
   change (((x j:ℤ):Per N)+_) - _= _
   rw [← Int.cast_natCast (R:=Per N) t.toNat, Int.toNat_of_nonneg hp]; change (((x j:ℤ):Per N)+p j)-(((-(r:ℤ)):ℤ)+p j)=_; unfold t; push_cast; ring

lemma fits (r:ℕ)(hr:D⊆Lattice.box r)(hk:2*r<c.val) : Fits c D:=by
   apply (wrap_injOn _).mono; intro x hx i; have hk' := box_test.mp (hr hx); have hl := hk'.1 i; have hh := hk'.2 i; omega

/-- Both forms. `hp` gives sup, `hb` gives integrated on the Pixel.
Location p arbitrary on the torus; output uniform, cost displayed explicitly. -/
lemma spends (X:Pixel c F)(W:Patch)(P:Site c)(he:Healing W X)(ht:Continuous X)(hv:Cvol X=1)(hE : Even c.val)(hc:4 ≤c.val)
    (a b:ℝ) (hp: ∀ U, ‖X U‖ ≤ Globe.expo a c)(hb: Bank.Stated X ≤ Globe.expo b c)
    (r:ℕ)(hD:D⊆ Lattice.box r)(hR:2*r+1+2*longM W ≤ c.val)(Z:Malt D F) :
    ‖Tide.fresh X (visit P Z)‖ ≤ Plum.quota W (2*r+1) a * Supply.budget Z ∧ ∀ w:ℝ, Coast w Z → ‖Tide.fresh X (visit P Z)‖ ≤ Plum.quota W (2*r+1) b * w:=by
     have hi:2*r<c.val:=by omega
     have hl:=fits r hD hi; have H: Fence (RP.square (leap P (fun _=>-(r:ℤ))) (fun _=>2*r+1)) (visit P Z):= (palps P Z).high (sail r hD hi P)
     exact ⟨Small.planetary he ht hv hE hc _ hR _ H (Supply.within Z P hl) a hp,fun w hw=> Bank.planetary he ht hv hE hc _ hR _ H (gainW P hl Z hw) b hb⟩
end YM.QCD.Agate.Paving
#print axioms YM.QCD.Agate.Paving.spends
