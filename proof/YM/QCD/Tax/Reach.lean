import YM.QCD.Tax.Grow
/-! # pricing full log. -/
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
variable (F)(G':ι→ℝ) {t h e ψ ξ μ' Λ w:ℝ}{w':ι→ℝ}
open Gas QCD.GasP Ursell
noncomputable def giant (G':ι→ℝ)(b:Costs)(h:ℝ) (p:Clusters Y.Bright):=∏ i,major Y G' b (p.2 i).val h
noncomputable def shadow (j k:ℕ)(g: Y.Bright → ℝ)(z:Clusters Y.Bright):= (1+(wag (seatP Y.lightF z) (radiusB s):ℝ))^k*badgeD Y j z g
noncomputable def smiler (k:ℕ)(B:ℕ):ℝ:= (1+2*(B:ℝ)+(4*(B:ℝ)+2))^k *polyPrice 1 k
lemma smearP (X:Support c)(B t:ℕ) (u:ℝ): (1+(wag X B:ℝ))^t *Real.exp (u*coverNumber B X) ≤ smiler t B *Real.exp ((u+1)*coverNumber B X):=by
    let v :ℝ:= coverNumber B X; let M:ℝ:=1+2*(B:ℝ)+(4*(B:ℝ)+2); have hv :0≤v:=Nat.cast_nonneg _; have h:0 ≤ M :=by unfold M; positivity
    have ht:1+(wag X B:ℝ) ≤ M*(1+v):=by unfold wag M; push_cast; unfold v; nlinarith
    have hh : (1+v)^t≤ polyPrice 1 t*Real.exp v:= by simpa only [one_mul] using! polynomial_cost (k:=t) (show (0:ℝ)<1 from zero_lt_one) hv -- syntax
    apply (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ht t) (Real.exp_pos _).le).trans; rw [mul_pow]; apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (pow_nonneg h _)) (Real.exp_pos _).le).trans_eq; unfold smiler; rw [add_mul,one_mul,Real.exp_add]; change M^t*_*_=M^t*_*_; ring
lemma escalates (u:Clusters Y.Bright)(p:Y.Bright→ℝ) (j :ℕ)(f:Y.Bright→ℝ):
    (∏ i,f (u.2 i))* badgeD Y j u p=clusters (blocked Y.lightF) (fun i=> f i*(dime j*p i)) u.2 :=by unfold badgeD clusters; simp_rw [prod_mul_distrib]; ring
lemma powered (u:Costs) (j m:ℕ)(p:Y.Bright →ℝ) (hz: ∀ i,0 ≤ p i)(hw:∀ i,1 ≤ G' i)(hf:1 ≤ h)(hq:0≤ u.markSeed) (hb : Ready Y.lightF (radiusB s) (fun i=> major Y G' u i.val h*(dime j*p i)) (e+1) Λ ψ t)(he:0 ≤e) : Ac.Hit (seatP Y.lightF) (radiusB s) (fun i=>giant Y G' u h i* shadow Y j m p i) e (smiler m (radiusB s)*(Λ*(1-t)⁻¹)):=by
    let X := Y.lightF; let V i:= major Y G' u (Subtype.val (i:Y.Bright)) h
    let W i:= V i*(dime j*p i); have hh: Ready X (radiusB s) W (e+1) Λ ψ t:=hb
    have hx i :0 ≤ giant Y G' u h i:= prod_nonneg fun j _=> zero_le_one.trans (majorPos Y G' u _ hf hw hq)
    have hp :0 ≤ dime j:=by unfold dime; positivity
    have hZ i :0 ≤ badgeD Y j i p:= clusters_nonneg _ (fun i'=>mul_nonneg hp (hz i')) _
    intro x; have hh:= log_hit_tail _ _ _ (literal_test _ (fun i:Y.Bright=> i.2.1.1)) hh (by linarith) 0 x
    have hs:0 ≤ smiler m (radiusB s):=by unfold smiler polyPrice; positivity
    simp only [Nat.zero_le,true_and,pow_zero,mul_one] at hh; apply budget_mono (budget_scale hs hh)
    · intro i; split; exact mul_nonneg (mul_nonneg (hx i) (mul_nonneg (by positivity : 0 ≤ (1+(wag (seatP Y.lightF i) (radiusB s):ℝ))^m) (hZ i))) (Real.exp_pos _).le; exact le_rfl
    intro i; split
    next hp=>
      change _ ≤ smiler m (radiusB s)* (if x∈ unionOf X i.2 then clusters (blocked X) W i.2 * currency (radiusB s) (e+1) (seatP X i) else 0); rw [if_pos (show x∈unionOf X i.2 from hp), show clusters (blocked X) W i.2= _ from (escalates Y i p j V).symm] -- adjust order
      let T:= seatP X i; let B:= radiusB s; let w:= (1+(wag T B:ℝ))^m; let a:= giant Y G' u h i; let z:=badgeD Y j i p
      change a*(w*z) *Real.exp (e*_) ≤ smiler m B* (a*z *Real.exp ((e+1)*_))
      have hh:=mul_le_mul_of_nonneg_left (smearP T B m e) (mul_nonneg (hx i) (hZ i)); refine le_trans (le_of_eq ?_) (hh.trans_eq ?_)
      · change _=a*z*(w* Real.exp _); unfold T X w; ring
      change a*z* _=smiler m B* (a*z *Real.exp ((e+1)*_)); unfold T X; ring
    next _=> exact (budget_scale hs hh).1 _
end YM.ConnectedActivityE6.Blaze.King
