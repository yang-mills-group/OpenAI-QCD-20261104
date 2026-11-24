import YM.QCD.King.Chapter
/-! # Ornamental spacecraft moment using labels per exceptional mark.
 Flexible multiplier not dependent on forest or mode. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.King
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Golden
open QCD QCD.Beam QCD.Loom Fleet QCD.Patron QCD.Cove PhysicalNext.Repeat.Greenbelt
open Push.AbsoluteSums Mixed Trees Reserves
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L : Side} {S : StepData c f} {T : Tube su S} {F : Forest S.ratio} {P : Teller su}
variable {j n l k : ℕ} {R : Rep su f} {X : Coat T F} {I : Finset (Tubular f su)} {η r q a W d C' A b s μ C v B: ℝ}
variable {Q : YM.ConnectedActivityE6.Target su P}{o :Target.Order su W}{H : Cash W s μ L Q o C T R} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V : E → Config su c} {x : E}
variable {χ:Chi}{ι:Type}{N:ℕ}(Y:Fleet H ι N){K:EvenA c N →+*EvenA c N}
local notation "I'"=> Pipe.Clump S ι
variable (Ξ : Utopia H j v η r C' χ)
set_option quotPrecheck false
open Pipe
variable {w':ι→ℝ}{Ω Λ Θ t u pu θ e:ℝ}
-- profile when Spinning
abbrev warm (Y:Fleet H ι N)(X:Coat T F)(z:Air f su)(l:ι)(V:E→ Config su c)(p:ℝ)(e:ℝ)(x:E):= fun i=>wearK c N e (Y.muscle l (vary X (V i)) (course X p R.beta z (V i)))
def windy (Y:Fleet H ι N)(a:ℝ)(i:ι):ℝ:= a*coverNumber (radiusB s) (Y.ground i)
-- choose state permit independent of forests. supply unsplit economics on same weights.
structure Enters (r A:ℝ)(Λ q:ℝ)(g:ι→ℝ)(e v η:ℝ)(χ:Chi)(j:ℕ)(X:ι→Site c)(T':Finset ι)(i n:ℕ):Prop where
 clock:0≤Λ
 pulse:0≤q
 cost:∀ i,0≤g i
 indoor :∀ (F:Forest S.ratio)(U:Coat T F),U.width=o.K → U.manifest → U.x=s → U.χ=χ → ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](x:E)(V:E → Config su c)(W:E → Directions su f)(z:Air f su), Mode V x j v → Clutch U z o.a R.beta η x j V W (fun i=> course U A R.beta z (V i)) → ∀ l,
   (Brush j (g l) (windy Y Λ l) (warm Y U z l V A e x) x ∨ l∈T'∧ ∃ k∈ Y.ground l,k∈ U.seeds.place∧ separation k (X l) ≤ i) ∧ Brush j (Real.exp q*g l) (windy Y Λ l) (warm Y U z l V A e x) x
 cover :∀ y,(T'.filter fun i=> X i=y).card≤ n
-- literal Lawn locations common floating measures. lands.
lemma south (Z:Finset ι)(f:ι→ E → EvenA c N)(v q:ι→ℝ)(h:∀ i∈Z,Brush j (v i) (q i) (f i) x): Brush j (∏ i∈Z,v i) (∑ i∈Z,q i) (fun p=>∏ i∈Z,f i p) x:=by
    induction Z using Finset.induction_on with
    | empty=> simp only [prod_empty,sum_empty]; simpa only [norm_one] using (certified (x:=x) (k:=j) (show (0:ℝ)≤0 from le_rfl) (1:EvenA c N))
    | insert i t hi ih=> simp_rw [prod_insert hi,sum_insert hi]; exact paints (h _ (mem_insert_self ..)) (ih (fun j hj=> h _ (mem_insert_of_mem hj)))
lemma applause {X:ι→ Site c}{T':Finset ι}(hw:Enters Y r A Λ t w' e v η χ j X T' k n):Guest Y r A Λ (t*((Animals.ballCost (k+1):ℝ)*n)) w' e v η χ j:=by
    refine ⟨hw.clock,hw.cost,?_⟩
    intro F u U hp he hh hv hQ hP hZ E _ _ _ x V W z hV hX
    have hv := hw.indoor F U hp he hh hv E x V W z hV hX
    let X' i:= warm Y U z i V A e x; let p':= u.toRight; let s:= p'.filter fun i=> ¬ Brush j (w' i) (windy Y Λ i) (X' i) x
    have hm i (h:i∈s):= (hv i).1.resolve_left (mem_filter.mp h).2
    have hz: s.card ≤ (Y.suitcase F).sizeP u*ballCost (k+1)*n:= Pipe.seedPop _ hP s X k
       (fun y=> (Finset.card_le_card (filter_subset_filter (fun i=> X i=y) (show s⊆ T' from fun j hj=> (hm j hj).1))).trans (hw.cover y)) fun j h=>by
         obtain ⟨k,hk,hY,hv⟩:= (hm j h).2; exact ⟨_,hY,(Y.suitcase F).leP u ((mem_filter.mp h).1) hk,hv⟩
    let P i:= if i∈ s then Real.exp t else 1
    have he' : (∏ i∈p',P i)= Real.exp (s.card*t):=by
       rw [Finset.prod_ite, show p'.filter (fun i=>i∈ s)=s from ?_, prod_const,prod_const_one,mul_one, Real.exp_nat_mul]; ext j; simp only [mem_filter]; exact and_iff_right_of_imp (fun h=> (filter_subset _ _) h)
    have hE:(∏ i∈p',P i)≤ Real.exp ((t*((ballCost (k+1):ℝ)*n))*↑((Y.suitcase F).sizeP u)):=by
        rw [he']; apply Real.exp_monotone; refine (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hz) hw.pulse).trans_eq ?_; push_cast; ring
    let f i:=P i*w' i
    apply Brush.shimmy _ (g:=fun i=>wearK c N e (Paint Y u _ _)) (show _=ᶠ[𝓝 x] fun p=>∏ i∈p',X' i p from Eventually.of_forall fun i=>map_prod ..)
    apply (south p' X' f (windy Y Λ) (fun i hi=> ?_)).climb
    · unfold f; rw [prod_mul_distrib]; exact mul_le_mul_of_nonneg_right hE (prod_nonneg fun _ _=> hw.cost _)
    · unfold windy; rw [← Finset.mul_sum]; apply mul_le_mul_of_nonneg_left _ hw.clock; apply le_trans _ (le_add_of_nonneg_left zero_le_one); exact le_add_of_nonneg_left (H.positive_volume _)
    by_cases h:i∈s
    · unfold f P; rw [if_pos h]; exact (hv i).2
    unfold f P; rw [if_neg h,one_mul]; exact of_not_not fun hz=>h (mem_filter.mpr ⟨hi,hz⟩)
lemma fuse {r:ℝ}{β:Type}(Z:Fleet H β N){X:ι→ Site c}{T':Finset ι}{W:β → Site c}{T'': Finset β}{z:β →ℝ}{n' k':ℕ}(hw:Enters Y r A Λ t w' e v η χ j X T' k n)(hv:Enters Z r A Θ t z e v η χ j W T'' k' n'): Enters (united Y Z) r A (max Λ Θ) t (Sum.elim w' z) e v η χ j (Sum.elim X W) (T'.disjSum T'') (max k k') (n+n'):=by
    refine ⟨hw.clock.trans (le_max_left ..),hw.pulse,?_,?_,?_⟩
    · rintro (i|i); swap; exact hv.cost i; exact hw.cost i
    · intro F U ht hX hc hf E _ _ _ x V W z₀ hV he; rintro (i|i)
      · obtain ⟨hu,hH⟩:= hw.indoor F U ht hX hc hf _ _ _ _ z₀ hV he i
        have he: windy Y Λ i ≤ windy (united Y Z) (max Λ Θ) (.inl i):=mul_le_mul_of_nonneg_right (le_max_left ..) (Nat.cast_nonneg _)
        exact ⟨hu.imp (fun h=> h.climb le_rfl he) (fun ⟨h,k,hx,hv,hZ⟩=>⟨inl_mem_disjSum.mpr h,k,hx,hv,hZ.trans (le_max_left ..)⟩),hH.climb le_rfl he⟩
      obtain ⟨hu,hH⟩:= hv.indoor F U ht hX hc hf _ _ _ _ z₀ hV he i
      have he: windy Z Θ i ≤ windy (united Y Z) (max Λ Θ) (.inr i):=mul_le_mul_of_nonneg_right (le_max_right ..) (Nat.cast_nonneg _)
      exact ⟨hu.imp (fun h=> h.climb le_rfl he) (fun ⟨h,k,hx,hv,hZ⟩=>⟨inr_mem_disjSum.mpr h,k,hx,hv,hZ.trans (le_max_right ..)⟩),hH.climb le_rfl he⟩
    intro y; rw [show Finset.filter (fun j=> Sum.elim X W j=y) (T'.disjSum T'')=(T'.filter fun j=>X j=y).disjSum (T''.filter fun j=>W j=y) from ?_,card_disjSum]; exact Nat.add_le_add (hw.cover y) (hv.cover y)
    ext i; rcases i with i|i <;> simp
end YM.ConnectedActivityE6.Blaze.King
