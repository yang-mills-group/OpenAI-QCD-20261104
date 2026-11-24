import YM.Massive.Reservoir.Craft
import YM.Massive.Reservoir.Pixels
import YM.QCD.Agate.Vast

/-! # Arcade: methods for the multiscale normalized Schwinger cylinders
on all scales with two different pressure sensitivities. A generic class
of well-controlled Regulator paths, hypotheses to discharge. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Cascade
open QCD QCD.Lat Lattice Wilson RG Pressure Gauge Function Filter Set QCD.Tide QCD.Rain QCD.Plum QCD.Agate QCD.Acre QCD.Acre.Rails QCD.Acre.Rails.Reference
open IV QCD.Agate.Supply QCD.Sparks QCD.Land
open MeasureTheory
open scoped Topology Matrix.Norms.L2Operator BigOperators Classical ComplexOrder
variable {n F : ℕ}{J: Patch}{K: KernelChoices}(h:J.Branches K su)(B:SparkMesh)
variable (N p:ℕ→ℕ)(A:∀ i,Run (fixed J K h) (N i) (B.n (p i)) F)
variable (u e :ℕ→ℝ)(v:ℝ)
set_option quotPrecheck false
local notation "S"=> fixed J K h
local notation "s" => fun i m : ℕ=>(fixed J K h).side (B.n (p i)) m
structure Arcade (u e : ℕ→ℝ)(v:ℝ) : Prop where
    act(i:ℕ): (A i).Actual
    light(j:ℕ) : Even (B.n j).val
    glow(j:ℕ) : 4 ≤ (B.n j).val
    stamp(j:ℕ) : B.n j=B.n 0*J.L^j
    pace : StrictMono N
    side : Tendsto (fun i=> (B.n (p i)).val) atTop atTop
    roof(i m:ℕ)(h':m≤N i) (U:Grid (s i m)) : ‖(A i).state m U‖≤ Globe.expo (u m) (s i m)
    prior(i m:ℕ)(h':m≤ N i) : Bank.Stated ((A i).state m) ≤ Globe.expo v (s i m)
    base(i m:ℕ)(h':m≤N i) : (A i).β m ∈ Set.Icc 1 (e m)
    factor(i m:ℕ)(h':m<N i) : (A i).w m∈ Set.Icc (1/2:ℝ) 2
variable (he: Arcade h B N p A u e v)
variable {u e v}
variable (ht: Arcade h B N p A u e v)
variable {D:Lot}
/-- Actual moment at centered placement; read values for active levels. This is
`joint` under `A.density`, normalized, via `Run.visible_ratio`. Pull of polynomial
`Malt` (on local links and Grassmann modes, any Borel coefficients). -/
noncomputable def sight (x:Malt D F)(m i:ℕ):ℂ:= (A i).visible m (Agate.visit (origin (s i m)) x)
-- omit he; no include until Lantern
include ht
lemma rises : Tendsto p atTop atTop:=by
    refine Filter.tendsto_atTop_atTop.mpr fun i=>?_ ;
    let T:=∑ k∈Finset.range i,(B.n k).val; obtain ⟨n,hn⟩:= eventually_atTop.1 (ht.side.eventually (eventually_gt_atTop T)); refine ⟨n,?_⟩; intro j hj; by_contra! h'; have hu: (B.n (p j)).val ≤ T:= Finset.single_le_sum (fun k _=> Nat.zero_le ((B.n k).val)) (Finset.mem_range.mpr h'); exact hu.not_gt (hn j hj)
lemma always (m:ℕ) : Tendsto (fun i=> (s i m).val) atTop atTop:=Filter.tendsto_atTop_mono' atTop (Eventually.of_forall fun _=> Nat.le_mul_of_pos_right _ ((S).ratio m|>.property)) ht.side

lemma signal {i m:ℕ}(hi:m≤ N i)(r:ℕ)(hr:D ⊆ Lattice.box r)(hk:2*r+1+2* longM J ≤ (s i m).val)(P: Site (s i m))(x:Malt D F):
    ‖(A i).visible m (Agate.visit P x)‖ ≤ quota J (2*r+1) (u m)* Supply.budget x ∧ ∀ w:ℝ, Coast w x → ‖(A i).visible m (Agate.visit P x)‖ ≤ quota J (2*r+1) v * w:=by
    obtain ⟨hL,hZ⟩:= (A i).standing (ht.act i) hi; have hp: Even (s i m).val:= Even.mul_right (ht.light _) _; have he:4 ≤ (s i m).val:= (ht.glow (p i)).trans (Nat.le_mul_of_pos_right _ ((S).ratio m|>.property)); exact Paving.spends _ _ P ((A i).state_health (ht.act i) hi) hL hZ hp he (u m) v (ht.roof i m hi) (ht.prior i m hi) r hr hk x
lemma sights (m:ℕ)(r:ℕ)(hr:D⊆Lattice.box r): ∀ᶠ i:ℕ in atTop, ∀ x:Malt D F,
    ‖sight h B N p A x m i‖≤ quota J (2*r+1) (u m)* Supply.budget x ∧ ∀ w:ℝ, Coast w x → ‖sight h B N p A x m i‖≤ quota J (2*r+1) v*w:=by
    filter_upwards [(always h B N p A ht m).eventually (eventually_ge_atTop (2*r+1+2*longM J)),ht.pace.tendsto_atTop.eventually (eventually_ge_atTop m)] with i hi he; exact fun x=>signal h B N p A ht he r hr hi _ x
lemma sAdd (x y:Malt D F){i m:ℕ}(hi:m≤N i): sight h B N p A (x+y) m i=sight h B N p A x m i+sight h B N p A y m i:=by unfold sight Run.visible; rw [map_add]; exact spell ((A i).standing (ht.act i) hi).1 (palps _ x).hp (palps _ y).hp
omit ht
lemma sMul (x:Malt D F)(z:ℂ)(i m:ℕ): sight h B N p A (z • x) m i=z • sight h B N p A x m i:=by unfold sight Run.visible; rw [map_smul]; exact spend ..
include ht
lemma sOne (D:Lot){i m:ℕ}(hi:m≤N i): sight h B N p A (1:Malt D F) m i=1:=by unfold sight Run.visible; rw [map_one,fresh1]; exact ((A i).standing (ht.act i) hi).2
lemma sSub (x y:Malt D F){i m:ℕ}(hi:m≤N i) : sight h B N p A (x-y) m i=sight h B N p A x m i-sight h B N p A y m i:=by apply eq_sub_of_add_eq; rw [← sAdd h B N p A ht (x-y) y hi,sub_add_cancel]

omit ht
-- Limit price both forms, all refs
structure Yield (P:ℕ→ScaleF F)(u:ℕ→ℝ)(J:Patch)(v:ℝ) : Prop where
   costs(m:ℕ)(D:Lot)(x:Malt D F)(r:ℕ)(hr:D⊆ Lattice.box r) : ‖(P m).mass D x‖≤ quota J (2*r+1) (u m)* Supply.budget x ∧ ∀ w:ℝ, Coast w x→ ‖(P m).mass D x‖ ≤ quota J (2*r+1) v*w

structure Glacial (l:Filter ℕ)(X:ℕ→ScaleF F)(V W:ℕ→ℝ): Prop where
   sites (m:ℕ) : Tendsto (fun i=> ((A i).β m, (A i).w m)) l (𝓝 (V m,W m))
   cylinders (m:ℕ)(D:Lot)(x:Malt D F) : Tendsto (sight h B N p A x m) l (𝓝 ((X m).mass D x))
lemma Arcade.subpath (f:ℕ→ℕ)(hf: StrictMono f)(ht:Arcade h B N p A u e v): Arcade h B (N∘f) (p∘f) (fun i=> A (f i)) u e v:=by
    exact ⟨fun i=>ht.act (f i),ht.light,ht.glow,ht.stamp,ht.pace.comp hf,ht.side.comp hf.tendsto_atTop,fun i m h U=> ht.roof _ _ h U,fun i m h=> ht.prior (f i) m h,fun i m h=> ht.base (f i) m h,fun i m h=> ht.factor _ _ h⟩ -- Lsp `∘d` likely not available replace.
end YM.Massive.Cascade
#print axioms YM.Massive.Cascade.signal
