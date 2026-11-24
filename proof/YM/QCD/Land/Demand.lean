import YM.QCD.Land.Council
import YM.Extraction.Simultaneous
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Local stability on a period route and simultaneous cylinder extraction

Thermodynamic on a fixed spacing. Does not assert uniqueness. Complex-valued local tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Land
open Lat Lattice RP Grass Extraction Function Finset Filter Topology
open scoped BigOperators Topology Matrix.Norms.Frobenius
variable {n : Side} {F : ℕ}

def half (t : ℕ) : Side := ⟨2^(t+1),by positivity⟩
def spanT (t : ℕ) : Side := ⟨2^(t+2),by positivity⟩
lemma twice (t : ℕ) : (spanT t).val=2*(half t).val := pow_succ' 2 _
lemma pairSpan (t) : Even (spanT t).val := by rw [twice]; simp
lemma half_le (t) : 2 ≤ (half t).val := by change 2 ≤ 2^(t+1); rw [pow_succ']; exact le_mul_of_one_le_right (by omega) (by apply Nat.succ_le_of_lt; positivity)
lemma floorsize (t : ℕ) : 4≤(spanT t).val := by have he := half_le t; rw [twice]; omega
lemma half_trend : Tendsto (fun t => (half t).val) atTop atTop := StrictMono.tendsto_atTop (strictMono_nat_of_lt_succ (by
  intro t; change 2^_ < 2^_; gcongr <;> omega))
lemma levels : Tendsto (fun t => (spanT t).val) atTop atTop := tendsto_atTop_mono (g:=fun t => (spanT t).val)
  (show (fun t => (half t).val) ≤ (fun t => (spanT t).val) from fun i => by show (half i).val ≤ (spanT i).val; rw [twice]; omega) half_trend

def bill (F : ℕ) (β m : ℝ) (t : ℕ) : Lat.Cut (spanT t) F := ⟨β,fun _ => (half t).val,m⟩

lemma encompassed (D : Lot) : ∃ q : ℕ, D ⊆ box q := by
  let v (x : Cover) : ℕ := univ.sup fun i : Axis => (x i).natAbs
  let Q := D.sup v
  refine ⟨Q,fun i hi => box_test.mpr ⟨fun j => ?_,fun j => ?_⟩⟩ <;>
    (have H : (i j).natAbs ≤ Q := (le_sup (s:=univ) (f:=fun j : Axis => (i j).natAbs) (mem_univ j)).trans (le_sup (f:=v) hi); omega)
lemma smooth_fit (D : Lot) : ∀ᶠ t : ℕ in atTop,Fits (spanT t) D := by
  obtain ⟨r,hr⟩ := encompassed D
  filter_upwards [levels.eventually (eventually_gt_atTop (2*r))] with t ht
  apply (wrap_injOn _).mono
  intro x hx i; have hk := box_test.mp (hr hx); have hl := hk.1 i; have hh := hk.2 i; omega

lemma size (D : Lot) : ∃ r : ℕ, ∀ᶠ t : ℕ in atTop, ∃ p : Site (spanT t),
    ∃ k : ℕ, 2^k*r=(spanT t).val ∧ Set.MapsTo (wrap (spanT t)) ↑D (RP.square p fun _ => r) := by
  obtain ⟨q,hq⟩ := encompassed D
  obtain ⟨u,hu⟩ := pow_unbounded_of_one_lt (2*q) (y:= (2:ℕ)) (by omega)
  refine ⟨2^u,?_⟩
  filter_upwards [eventually_ge_atTop u, levels.eventually (eventually_gt_atTop (2*q))] with t ht hn
  let n := spanT t
  refine ⟨wrap n (fun _ => -(q:ℤ)),t+2-u,by rw [← pow_add,Nat.sub_add_cancel (by omega)]; rfl, fun x hx i => ?_⟩
  have hl := (box_test.mp (hq hx)).1 i; have hh := (box_test.mp (hq hx)).2 i
  let a := x i + q
  have he : 0 ≤ a := by unfold a; omega
  have hv : a ≤ ((2*q:ℕ):ℤ) := by unfold a; omega
  change ((wrap n x i)-(wrap n (fun _ => -(q:ℤ))) i).val < _
  rw [show wrap n x i - _=(a.toNat:Per n) by
    change (x i : Per n)-(Int.cast (R:=Per n) (- (q:ℤ)))=(a.toNat:Per n)
    rw [← Int.cast_natCast (R:=Per n) a.toNat,Int.toNat_of_nonneg he]; unfold a; push_cast; ring,
    ZMod.val_natCast_of_lt]
  · change a.toNat < 2^u; exact lt_of_le_of_lt (by omega) hu
  change 2*q<n.val at hn; omega

structure Sound (F : ℕ) (β m : ℝ) : Prop where
  hb : 0 ≤ β
  floor : ∃ b : ℝ, 0<b ∧ ∀ t, b^sites (spanT t) ≤ (bill F β m t).partitionR
lemma sound_zero (F : ℕ) (β : ℝ) (hb : 0≤β) (m : ℝ) (hm : 0≤m) : Sound F β m := by
  obtain ⟨c,b,hc,h,H⟩ := stable
  refine ⟨hb,b*(Real.exp (-2*β*pl)*c^(12*F)),by positivity,fun t => (H (spanT t) F (bill F β m t) hb (Or.inl hm)).1⟩ -- check inference

variable {β m : ℝ} (s : Sound F β m)
lemma Sound.positive (s : Sound F β m) (t) : 0<(bill F β m t).partitionR := by
  obtain ⟨b,hb,H⟩ := s.floor
  exact lt_of_lt_of_le (by positivity) (H t)
lemma Sound.near (s : Sound F β m) (D : Lot) : ∃ A : ℝ, 0≤A ∧ ∀ᶠ t : ℕ in atTop, ∀ x : Cyl D F,
    ‖tally (bill F β m t) D x‖ ≤ A*‖x‖ := by
  obtain ⟨r,hr⟩ := size D
  obtain ⟨b,hp,H⟩ := s.floor
  obtain ⟨a,ha,h⟩ := council_cost D F
  let K := ((101+|m|)^(12*F)/b)^(r^4)
  have he : 0 ≤ K := by unfold K; positivity
  refine ⟨K*a,mul_nonneg he ha,?_⟩
  filter_upwards [hr,smooth_fit D] with t ht hz
  intro x; obtain ⟨q,k,hk,hq⟩ := ht
  have hh : Floors _ _ := locates (spanT t) (council x) _ hq
  have hi := allows hk (pairSpan t) (floorsize t) hp (H t) s.hb _ _ hh (issue_inv (council_stains x))
  rw [← council_tally (bill F β m t) x hz s.hb]
  exact hi.trans (by rw [mul_assoc K]; exact mul_le_mul_of_nonneg_left ((issue_price hz _).trans (h x)) he)

-- diagonal on a countable dense set of functions; no hidden row limits.
instance (D : Lot) (F : ℕ) : SecondCountableTopology (Cyl D F) := by
  unfold Cyl
  haveI : SecondCountableTopology (Trace D) := by unfold Trace; infer_instance
  haveI : SecondCountableTopology (Poly D F) := by
    haveI : ProperSpace (Poly D F) := FiniteDimensional.proper ℂ _; exact secondCountable_of_proper
  infer_instance

lemma takeAt {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A] (f : ℕ → A →ₗ[ℂ] ℂ) (D : Set A)
    (h : Dense D) (r : ℝ) (hr : 0≤r) (hp : ∀ᶠ i in atTop, ∀ x, ‖f i x‖ ≤ r*‖x‖)
    (he : ∀ x∈D,CauchySeq (fun i => f i x)) (x : A) : ∃ z, Tendsto (fun i => f i x) atTop (𝓝 z) := by
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff]; intro ε hε
  obtain ⟨y,hy,hd⟩ := Metric.mem_closure_iff.mp (h x) (ε/(4*(r+1))) (by positivity)
  have hh : r*‖x-y‖ < ε/3 := by rw [dist_eq_norm] at hd; rw [lt_div_iff₀ (by positivity)] at hd; nlinarith [norm_nonneg (x-y)]
  obtain ⟨j,hj⟩ := eventually_atTop.mp hp
  obtain ⟨m,hm⟩ := Metric.cauchySeq_iff.mp (he y hy) (ε/3) (by positivity)
  have H (i) (hi : max j m ≤ i) : dist (f i x) (f i y) < ε/3 := by rw [dist_eq_norm,← map_sub]; exact lt_of_le_of_lt (hj i (by omega) (x-y)) hh
  refine ⟨max j m,fun i hi k hk => ?_⟩
  have hk₁ := H i hi; have hk₂ := H k hk; have hk₃ : dist (f i y) (f k y)<ε/3 := hm i (by omega) k (by omega)
  change dist (f i x) (f k x)<_
  have hw := dist_triangle (f i x) (f i y) (f k x); have hx := dist_triangle (f i y) (f k y) (f k x); rw [dist_comm] at hk₂; linarith

/-- A thermodynamic hierarchy yet to be equipped with spatial symmetries and RP. -/
structure LocalState (F : ℕ) where
  amp (D : Lot) : Cyl D F →L[ℂ] ℂ
  agrees {D S : Lot} (h : D⊆S) (x : Cyl D F) : amp S (crowd h x)=amp D x
  one (D : Lot) : amp D 1=1
  stains {D : Lot} (x : Cyl D F) (k : Town D) : amp D (stainX k x)=amp D x

def Exhausts (β m : ℝ) (k : Extraction.Sequence) (f : LocalState F) :=
  ∀ D : Lot, ∀ x : Cyl D F, Tendsto (fun i => tally (bill F β m (k i)) D x) atTop (𝓝 (f.amp D x))

theorem city_limits (s : Sound F β m) : ∃ k : Extraction.Sequence, ∃ f : LocalState F, Exhausts β m k f := by
  choose d hd hD using fun D : Lot => TopologicalSpace.exists_countable_dense (Cyl D F)
  haveI (D : Lot) : Countable ↥(d D) := hd D
  let I := (D : Lot) × ↥(d D)
  let N := fun t : ℕ => bill F β m t
  choose A hA W using s.near
  obtain ⟨k,f,hf⟩ := Extraction.simultaneous (fun p : I => fun t => tally (N t) p.1 p.2.val)
    (K := fun p => Metric.closedBall 0 (A p.1 * ‖p.2.val‖)) (fun _ => isCompact_closedBall ..)
    (fun p => (W p.1).mono fun i H => by
      rw [Metric.mem_closedBall, dist_zero_right]; exact H p.2.val)
  let y := fun (D : Lot) i => tally (N (k i)) D
  choose G hG using fun D => takeAt (y D) _ (hD D) _ (hA D) (k.cofinal.eventually (W D))
    fun x hx => ((hf ⟨D,x,hx⟩).2).cauchySeq
  let L (D : Lot) : Cyl D F →ₗ[ℂ] ℂ :=
    { toFun := G D
      map_add' := fun x z => tendsto_nhds_unique (hG _ _) (((hG D x).add (hG D z)).congr (fun i => (map_add (y D i) _ _).symm))
      map_smul' := fun c x => tendsto_nhds_unique (hG _ _) ((tendsto_const_nhds.smul (hG D x)).congr (fun i => (map_smul (y D i) c x).symm)) }
  let X (D : Lot) := LinearMap.mkContinuous (L D) (A D) (fun x => le_of_tendsto (hG D x).norm
    ((k.cofinal.eventually (W D)).mono fun _ H => H x))
  refine ⟨k,⟨X,fun h x => ?_,fun D => ?_,fun x v => ?_⟩,hG⟩
  · apply tendsto_nhds_unique (hG _ (crowd h x)) ((hG _ x).congr (fun i => ?_))
    simp only [y,tallying, respect]
  · apply tendsto_nhds_unique (hG D 1) (tendsto_const_nhds.congr (fun i => ?_))
    simp only [y,tallying,issue_one]; exact (Lat.Cut.vacuum _ (Sound.positive s _)).symm
  exact tendsto_nhds_unique (hG _ (stainX v x)) ((hG _ x).congr' ((k.cofinal.eventually (smooth_fit _)).mono (fun i hi => (issued_stained _ _ hi v).symm)))
end YM.QCD.Land
