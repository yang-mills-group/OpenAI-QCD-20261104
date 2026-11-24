import YM.QCD.King.Stone
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Horns
/-! # sell simultaneous shape, any uplift of Mater heights with same Ξ. -/
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
-- Mark magnification separated from global scale. denominator cancellation later.
def grate (j k:ℕ) (m:ℝ) (W:Piece S ι→ℝ): Y.Bright →ℝ:=fun i=>stewP Y j k m W i.val
def shareP (v: I') : ℝ:=↑(Y.shellF.sizeP v)
def coron (S:StepData c f)(ι:Type)(i:Piece S ι):ℕ:=Sum.elim (Sum.elim (fun _=>0) Silica.horn) (fun _=>0) i
def heft (S:StepData c f)(p:Pipe.Clump S ι):= p.card+∑ i∈p, coron S ι i
def major (S₀:Costs)(z:I') (h:ℝ):= h^(heft S z)*(∏ i∈z.toRight,G' i)*Real.exp (Q.ε*worthX Y z)*Real.exp (S₀.markSeed*shareP Y z)
lemma majorPos (S₀:Costs)(z:I')(hr:1≤h)(hp:∀ i,1≤G' i)(he:0≤S₀.markSeed):1 ≤ major Y G' S₀ z h:=one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hr) (one_le_prod fun i _=> hp _)) (Real.one_le_exp (mul_nonneg Q.usable.le (worthG Y _).2))) (Real.one_le_exp (mul_nonneg he (Nat.cast_nonneg _)))
include Y in
lemma tagPos {w:ι→ℝ}(h: ∀ i,0 ≤ w i) (e t:ℝ)(i:Piece S ι):0 ≤ checkL Ξ w e t i :=by
    let p:= checkL Ξ w e t i; have hC:(∏ j∈({i}:I'),checkL Ξ w e t j)=p:=prod_singleton ..; let S':Forest S.ratio:= Classical.choice (Tree.select S.ratio S.patch.odd_side); rw [checkX (F:=S') Y ..] at hC; rw [show checkL Ξ w e t i=p from rfl,← hC]; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (prod_nonneg fun _ _=>Ξ.fares _) (prod_nonneg fun i _=> h _))
noncomputable def ware (Q:Target su P) (z h r q:ℝ)(j m:ℕ):= dime j*z*(polyPrice Q.ε m*(h*r*(1-q)⁻¹))
lemma gateQ {a t:ℝ}{w:ι→ℝ}(h:ℝ)(hh:0≤h)(hk:h ≤PhysicalNext.Repeat.Height.grow su L s) (he:Heavy Ξ)(hw:∀ i,0≤ w i)(hp: (unitsP Q L μ R.beta s C' a t).Buy S.patch.L Q.halo (radiusB s))(hv: Ac.Hit Y.ground (radiusB s) w Q.relative t) :
 let P':= unitsP Q L μ R.beta s C' a t
 Ready (Y.suitcase F).gP (radiusB s) (tariff ((fun i=>h^(coron S ι i)*checkL Ξ w a t i)) ((Y.suitcase F).inks P' (fun _=>0)) (fun i=>P'.markSeed*(Y.suitcase F).tenants i) Q.ε) (P'.exponent+2*Q.ε) P'.rootHit P'.reserveTree P'.q:=by
   intro P'; let K:= Sum.elim H.birth Y.ground; let G i:=h^horn i*Ξ.flair i; let Z:=Sum.elim G w; let X:=Sum.elim (ConnectedActivityE6.lengths T R) (fun _:ι=>0); let B:=radiusB s
   have hK: Sales _ _ _ _ G _ _:= Sales.shift he (A:=1) zero_le_one (fun i=>mul_nonneg (pow_nonneg hh _) (Ξ.accrues.holds i)) (fun i=> by rw [one_mul]; exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hh hk _) (Ξ.accrues.holds _))
   rw [one_mul] at hK
   have hx: Accounts S Q.halo B P' K Z X (steamP S P'):=by
     refine ⟨fun i _=> ⟨mul_nonneg hp.capture (Real.exp_pos _).le,le_rfl⟩,?_,?_,?_⟩
     · rintro (i|i); exact mul_nonneg (pow_nonneg hh _) (Ξ.accrues.holds i); exact hw i
     · rintro (i|i); exact Ξ.accrues.extra i; exact le_rfl
     intro i
     let U:=tariff w (fun _=>0) (fun _=>0) Q.ε
     have he: U=w:=by ext i; simp [U,tariff]
     convert! Labels.together _ _ _ hK.hit (he.symm ▸ hv) i using 1 -- name/options projection
     ext k
     rcases k with k|k <;> rfl
   have he:= Mixed.ready_vertices S Q.halo B P' _ _ _ _ hp hx
   let U:=shifts S ι
   refine ⟨he.1,he.2.1,he.2.2.1,he.2.2.2.1, ?_,fun i=>?_⟩ -- Sec
   · rintro i; apply mul_nonneg (mul_nonneg (pow_nonneg hh _) (tagPos Y Ξ hw _ _ _)) (Real.exp_pos _).le
   next i =>
     convert! budget_pull U U.injective (he.2.2.2.2.2 i) using 1; ext j
     rcases j with (i|i)|i
     · simp only [coron,Sum.elim, pow_zero, tariff, one_mul]; rfl
     · rfl
     simp only [coron,Sum.elim,pow_zero,tariff,one_mul]; rfl

lemma brew (hr:Heavy Ξ)(hh:h ≤ PhysicalNext.Repeat.Height.grow su L s)(hv:∀ i,1 ≤ G' i) (hz:1 ≤ h) (hw:∀ i,0 ≤ w' i)(hp:Ac.Hit Y.ground (radiusB s) (fun i=>G' i*w' i) Q.relative t)
 (ht : (unitsP Q L μ R.beta s C' e t).Buy S.patch.L Q.halo (radiusB s))(z:ℝ)(k:ℕ)(he:0 ≤ z)(hQ: degreePrice (radiusB s) (h*(unitsP Q L μ R.beta s C' e t).rootHit) Q.δ ≤1/2):
 let b:= unitsP Q L μ R.beta s C' e t; let W:=checkL Ξ w' e t; let f i:=dime j*(grate Y j k z W i); Ac.Hit Y.lightF (radiusB s) (fun i=> major Y G' b i.val h*f i) Q.exp (ware Q z h b.rootHit (1/2) j k) :=by
    intro b W f'; let F:=Classical.choice (Tree.select S.ratio S.patch.odd_side); let U:= Y.suitcase F
    let f:=fun i=> G' i*w' i; let ω' (i:Piece S ι) := h^ coron S ι i *checkL Ξ f e t i; let v i:= h* ω' i; let P:= U.inks b (fun _=>0); let Z':= Y.lightF; let q i:= b.markSeed*U.tenants i; let a:=tariff ω' P q Q.ε
    have he' : 0≤ h:=zero_le_one.trans hz; have hg i:0 ≤ f i:=mul_nonneg (zero_le_one.trans (hv i)) (hw _)
    let B:=radiusB s; let Z i:=tariff v P q Q.ε i
    have hA:Ready U.gP B a (b.exponent+2*Q.ε) b.rootHit b.reserveTree b.q:= King.gateQ F Y Ξ h he' hh hr hg ht hp
    have hs i:Z i=h*a i:=by unfold Z v a tariff; ring
    have hv i:0≤ ω' i:=mul_nonneg (pow_nonneg he' _) (tagPos Y Ξ hg _ _ _); have hδ:=Q.usable
    have hW: Ready U.gP B Z (Q.exp+2*Q.ε) (h*b.rootHit) b.reserveTree b.q :=⟨mul_pos (lt_of_lt_of_le zero_lt_one hz) hA.1,hA.2.1,hQ,hA.2.2.2.1,(fun i=> by rw [hs]; exact mul_nonneg he' (hA.2.2.2.2.1 _)),QCD.Jets.Sun.heights_factor h _ _ _ hA.2.2.2.2.2 hs he'⟩
    have hT z': (∏ i∈z',v i) = h^(heft S z')*(∏ i∈z'.toRight,G' i)*∏ i∈z',W i:=by
       unfold v W; rw [prod_mul_distrib,prod_const,checkX (F:=F) Y Ξ w' e t z',show ∏ i∈z',ω' i=h^(∑ i∈z', coron S ι i)*∏ i∈z',checkL Ξ f e t i from (by unfold ω'; rw [prod_mul_distrib,Finset.prod_pow_eq_pow_sum]),checkX (F:=F) Y Ξ f e t z']; unfold f; rw [Finset.prod_mul_distrib]; unfold heft; rw [pow_add]; ring
    let N':=polyPrice Q.ε k; have hk:0 ≤ N':=by unfold N' polyPrice; positivity
    have hm:dime j≥0:=by unfold dime; positivity
    let C:=dime j*z*N'; have hC:0 ≤ C:=by unfold C; positivity
    intro x
    have hY:= budget_pull (fun i:Y.Bright=>i.val) Subtype.val_injective (touch_tail U.gP B hW x 0); simp only [Nat.zero_le,pow_zero,mul_one,if_true] at hY
    unfold ware; rw [show dime _*_ *(_*_) = C*(h*b.rootHit*(1-b.q)⁻¹) from ?_]; rotate_left
    · unfold C N'; rw [show b.q=1/2 from rfl]; ring
    apply budget_mono (budget_scale hC hY)
    · intro i; split; swap; · exact le_rfl
      have hx:0 ≤ grate Y j k z W i:= mul_nonneg (mul_nonneg he (prod_nonneg fun j _=> tagPos Y Ξ hw _ _ j)) (pow_nonneg (add_nonneg zero_le_one (worthG Y _).2) _) -- fix
      have hi:0≤ major Y G' b i.val h:= (zero_le_one (α:=ℝ)).trans (majorPos Y G' b i.val hz (by assumption) ht.marked)
      exact mul_nonneg (mul_nonneg hi (mul_nonneg hm hx)) (Real.exp_pos _).le
    intro i; split
    next he=>
      let Y':= Ξ; let p:=i.val; let H:=Z' i; let w:=worthX Y p
      have hP: touches U.gP B Z (Q.exp+2*Q.ε) x p= touches U.gP B v Q.exp x p*Real.exp (2*Q.ε*w+b.markSeed *U.sizeP p):=by
         rw [show Z=tariff v P q Q.ε from rfl,set_exchange]; rw [show (∑ i∈p, weight U.gP B P i)=w from scoreY (F:=F) Y e t p]; refine congr_arg (fun j=> touches U.gP B v Q.exp x p* Real.exp (2*Q.ε*w+j)) ?_
         unfold q; rw [← mul_sum]; simp only [tenants]; rw [← Nat.cast_sum]; rfl
      change _≤ C* touches U.gP B Z (Q.exp+2*Q.ε) x i.val; rw [show i.val=p from rfl,hP]
      have hh: Ac.Spark U.gP p:=i.2.1.2.1
      have hu : x∈ p.biUnion U.gP:=he
      have hx: touches U.gP B v Q.exp x p=(∏ i∈p,v i)*(∏ i∈p, currency B Q.exp (U.gP i)):= (if_pos ⟨hh,hu⟩).trans (prod_mul_distrib ..)
      let q':=h^(heft S p)*∏ i∈p.toRight,G' i; let q₁:=∏ i∈p,W i; let S':= Real.exp (Q.ε*w); let W':= Real.exp (b.markSeed* ↑(U.sizeP p))
      have he':coverNumber B H ≤∑ i∈p,coverNumber B (U.gP i):= Ac.cover U.gP B hh
      have he:currency B Q.exp H ≤ ∏ i∈p,currency B Q.exp (U.gP i):=by unfold currency; rw [← Real.exp_sum,← mul_sum,← Nat.cast_sum]; exact Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr he') Q.bound)
      have hp': 0≤q':= mul_nonneg (by positivity) (prod_nonneg fun i _=> zero_le_one.trans ((by assumption:∀ i,1≤G' i) i))
      have hg₁:0≤q₁:= prod_nonneg fun i _=> tagPos Y Ξ hw _ _ i
      have hz₁:0≤w:= (worthG Y _).2; have hS:0≤S':=(Real.exp_pos _).le; have hW:0≤W':=(Real.exp_pos _).le
      rw [hx,hT,Real.exp_add,show 2*Q.ε*w=Q.ε*w+Q.ε*w by ring,Real.exp_add]
      change q'*S'*W'*(dime j*(z*q₁*(1+w)^k))*currency B Q.exp H ≤ C* (q'*q₁*(∏ i∈p,currency B Q.exp (U.gP i))*(S'*S'*W'))
      calc _ ≤ q'*S'*W'*(dime j*(z*q₁*(N'*S')))*(∏ i∈p,currency B Q.exp (U.gP i)):=by
                    have hv : (1+w)^k≤ N'*S':= polynomial_cost Q.usable hz₁ _; have hx:0≤currency B Q.exp H:=(Real.exp_pos _).le; gcongr -- z shadow he
           _ = _ := by unfold C; ring
    next h=> exact (budget_scale hC hY).1 i
end YM.ConnectedActivityE6.Blaze.King
