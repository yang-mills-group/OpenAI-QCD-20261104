import YM.Cardinal.Schools
/-! # Stamp costs transport across gauge anchors and rescalings.Mon. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place Module
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
namespace Plans
variable {a b t θ v:ℝ}{k d n j:ℕ}{c:Side}
open Pipes Lining Lining.Ferry
open Pressure Garden Run Laurent Carrier Next.Free
open Beacon MultiNext.SignedSource Stative
open Counting Counting.Click Terrain Display Costs Sieve Chute Papyrus Facets
open MassiveQCD.Plate Card Iris QCD.Cove QCD.Kites QCD.Stew Push.Local
namespace Girdle
variable {P:BudgetPoint}{o o':Site c}{Y:Support c}
local notation "K"=> Keys c 6
variable (h:separation o o' ≤ n)(G F:Grid c →Lat.Fields c 6)
def shift (n:ℕ)(k:ℕ):ℝ:= (1+(n:ℝ))^k
def tariff (n finish power orders:ℕ):ℝ:= (shift n power)^orders*shift n finish
variable (H:Sight Y o k P t G a)(hv:0<t)
include h
lemma shoulder (i:Site c)(k:ℕ) : (1+(separation i o':ℝ))^k ≤ shift n k*(1+(separation i o:ℝ))^k:=by
    have hp : (separation i o':ℝ) ≤ (separation i o:ℝ)+(n:ℝ):=by exact_mod_cast (separation_triangle i o o').trans (add_le_add_right h _)
    rw [shift,← mul_pow]; apply pow_le_pow_left₀ (by positivity); nlinarith only [hp,mul_nonneg (Nat.cast_nonneg (α:=ℝ) (separation i o)) (Nat.cast_nonneg (α:=ℝ) n)]
lemma luggage (A:Directions su c)(hk:P.dirBound o' A): P.dirBound o ((shift n P.power)⁻¹ • A):=by
    intro i; let S:=shift n P.power; have ht:1 ≤ S:=one_le_pow₀ (by simp)
    change ‖S⁻¹ • A i‖ ≤ _; rw [norm_smul,Real.norm_of_nonneg (by positivity)]; apply (inv_mul_le_iff₀ (zero_lt_one.trans_le ht)).2
    exact (hk i).trans ((mul_le_mul_of_nonneg_left (shoulder h _ P.power) P.threshold_pos.le).trans_eq (by ring)) -- ring knows reduc.
lemma taxView (f: Lat.Fields c 6)(k:ℕ)(t:ℝ)(hz:0≤ t): view o' k f t ≤ shift n k*view o k f t:=by
    unfold view; rw [Finset.mul_sum]; apply sum_le_sum; intro i _; unfold MassiveQCD.Plate.toll; rw [← mul_assoc (_:ℝ),← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); apply mul_le_mul_of_nonneg_right _ (by positivity); let V':=i.sup (lens o); let V:=i.sup (lens o'); have hp:V ≤ V'+n:= Finset.sup_le fun j hj=> (separation_triangle (locationP j) o o').trans (add_le_add (Finset.le_sup (f:=lens o) hj) h)
    have hh: (V:ℝ) ≤ (V':ℝ)+(n:ℝ):=by exact_mod_cast hp
    rw [shift,← mul_pow]; apply pow_le_pow_left₀ (by positivity); change 1+(V:ℝ)≤ _*(1+(V':ℝ)); nlinarith only [hh,mul_nonneg (Nat.cast_nonneg (α:=ℝ) V') (Nat.cast_nonneg (α:=ℝ) n)]
include H hv
lemma moving : Sight Y o' k P t G (tariff n k P.power P.order *a):=by
    let S:= shift n P.power; have hS:1 ≤ S:=one_le_pow₀ (by simp); have Hf (i:ℕ):0<shift n i:=by unfold shift; positivity
    have hx:=H.travels
    refine ⟨H.room,H.gate,H.use,fun V hV l hl hp=>?_, H.borel,by unfold tariff shift; positivity ⟩
    let U:=leftDerivs G l V; let f:=MassiveQCD.Plate.view o k U t; let p:=l.map (fun A: Directions su c=> S⁻¹ • A); have hh : (S^l.length)⁻¹*f≤ a:=by
       have hz:=H.pole V hV p (by unfold p; rwa [List.length_map]) (by intro i hi; obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hi; exact luggage h _ (hp j hj)); have hu:leftDerivs G p V=(S⁻¹^l.length) • U:=left_homogeneous l (H.use V hV) hl _; rw [hu] at hz; apply le_trans (le_of_eq ?_) hz
       change _ = view o k ((↑(S⁻¹ ^ l.length):ℂ) • U) t; rw [viatic,Complex.norm_real, Real.norm_of_nonneg (by positivity),inv_pow]
    refine (taxView h U k _ hv.le).trans ?_; apply le_trans (mul_le_mul_of_nonneg_left ((inv_mul_le_iff₀ (by positivity : 0<S^l.length)).1 hh) (Hf _).le); exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hS hl) hx) (Hf _).le).trans_eq (by unfold tariff; change _*(S^_*a)=S^_*_*a; ring)
omit H
include hv
variable (hF:Flame G P Y o t d j a) (hp : 0<v)
include hF
set_option maxHeartbeats 720000 in
lemma frameMove (i:ℕ)(hs:i<j) (U:Alg K) : ‖framesF (purseX o' d t) (mantel i U)‖ ≤ (shift n d)^j * ‖framesF (purseX o d t) (mantel i U)‖:=by
    change Creek.load _ _ ≤ _ * Creek.load _ _; rw [Creek.dry _ (purse_pos _ _ _ hv),Creek.dry _ (purse_pos _ _ _ hv),mul_sum]; apply sum_le_sum; intro X _; let S:= shift n d; have hS:1 ≤ S:=one_le_pow₀ (by simp)
    -- spectrum
    by_cases h': X.card=i
    · rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      calc
        _ ≤ ∏ k∈X,(S*purseX o d t k):= by apply Finset.prod_le_prod (fun k _=> (purse_pos _ _ _ hv _).le); intro k _; exact (mul_le_mul_of_nonneg_left (shoulder h (locationP k) d) hv.le).trans_eq (show _=S*_ from (by change t*(S*_)=S*(t*_); ring))
        _ ≤ _:=by rw [prod_mul_distrib,prod_const]; apply mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hS (h'.symm ▸ hs.le)) (prod_nonneg fun i _=> (purse_pos _ _ _ hv _).le)
    rw [show coef X (mantel i U)=0 from (angel i X U).trans (if_neg h'),norm_zero,mul_zero,mul_zero,mul_zero] -- arguments
abbrev price (n k m d j:ℕ):ℝ:= Girdle.tariff n 2 k m+(shift n k)^m*(shift n d)^j
lemma living : Flame G P Y o' t d j (price n P.power P.order d j*a):=by
   let S:= shift n P.power; have hS:1 ≤ S:=one_le_pow₀ (by simp); have hW(i):0<shift n i:=by unfold shift; positivity
   let p₀:=price n P.power P.order d j; have hη:0≤tariff n 2 P.power P.order:=by unfold tariff shift; positivity
   have hA:=hF.sight.travels; have hp:0≤p₀:=by unfold p₀ price; apply add_nonneg hη; unfold shift; positivity
   refine ⟨padded _ (mul_le_mul_of_nonneg_right ?_ hA) (moving h G hF.sight hv), fun i hi=> ⟨mul_nonneg hp hA,fun V hV l hl hv'=>?_⟩⟩; · exact le_add_of_nonneg_right (by unfold shift; positivity) -- `a≤a+`
   let A:=(framesF (purseX o d t)).comp (mantel i); let B:=(framesF (purseX o' d t)).comp (mantel i); let X:=leftDerivs G l V; let W:= ‖A X‖; change ‖leftDerivs (B ∘ G) l V‖ ≤ _; rw [left_linear _ _ (hF.sight.use V hV) hl]; have he:= frameMove h G hv hF i hi X
   let z:=l.map (fun A:Directions su c=> S⁻¹ • A); have hz:z.length≤P.order:=by unfold z; rwa [List.length_map]
   have hb:=hF.issues i hi|>.2 V hV z hz (by intro j hj; obtain ⟨k,hk,rfl⟩:= List.mem_map.mp hj; exact luggage h _ (hv' k hk)); change ‖leftDerivs (A ∘ G) z V‖≤a at hb; rw [left_linear _ _ (hF.sight.use V hV) hz, show leftDerivs G z V=S⁻¹ ^ l.length • X from left_homogeneous _ (hF.sight.use V hV) hl _,map_smul,norm_smul,Real.norm_of_nonneg (by positivity),inv_pow] at hb
   apply he.trans; exact (mul_le_mul_of_nonneg_left ((inv_mul_le_iff₀ (by positivity : 0<S^l.length)).1 hb) (by positivity [hW d] : 0 ≤ shift n d^j)).trans (by
       change shift n d^j * _ ≤ _; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hS hl) hA) (by unfold shift; positivity)); rw [←mul_assoc, mul_comm (_^j)]; apply mul_le_mul_of_nonneg_right _ hA; exact le_add_of_nonneg_left hη)
omit h
variable (hr:0<θ)(hξ:θ*v ≤ t)
-- output θ endpoint read, v field rescale.Engine∘G
include hr hξ hp
lemma orbitG : Flame (engine v K∘G) P Y o θ d j a:=by
    let X:=(engine v K).toLinearMap.toContinuousLinearMap.restrictScalars ℝ; let F:= X ∘ G; let H:=hF.sight; have hX(i U): mantel i (engine v K U)=engine v K (mantel i U):=Pika ..
    refine ⟨⟨fun i j e=> congr_arg X (H.room _ _ e),fun i=>hopeful 6 v _ _ (H.gate _),fun V hV=> X.contDiff.contDiffAt.comp (f:=G∘increment V) 0 (H.use V hV),fun V hV l hl hh=> ?_, X.measurable.comp H.borel,H.travels⟩,fun i hi=>⟨H.travels,fun V hV l hl hh=>?_⟩⟩
    · change view o 2 (leftDerivs F l V) θ≤_; rw [show leftDerivs F l V=_ from left_linear X l (H.use V hV) hl, show X (leftDerivs G l V)=engine v K _ from rfl, changeView o _ _ hr.le hp.le, mul_comm v]; exact (birthView o _ _ (mul_pos hr hp).le hξ).trans (H.pole V hV _ hl hh)
    let U:=leftDerivs G l V; let A:= framesF (purseX o d t); let B:= framesF (purseX o d θ); let V':= (A.comp (mantel i)); let W':=B.comp ((mantel i).comp X); have he:= (hF.issues i hi).2 V hV l hl hh; change ‖leftDerivs (V' ∘ G) l V‖ ≤ _ at he; rw [left_linear V' _ (H.use V hV) hl] at he; change ‖leftDerivs (W' ∘ G) l V‖≤ _; rw [left_linear W' _ (H.use V hV) hl]; apply le_trans _ he; change Creek.load (purseX o d θ) (mantel i (engine v K U))≤Creek.load _ (mantel i U); rw [hX,Creek.dry _ (purse_pos _ _ _ hr),Creek.dry _ (purse_pos _ _ _ hv)]; apply Finset.sum_le_sum; intro X _; rw [fundW,norm_mul,norm_pow, Complex.norm_real,Real.norm_of_nonneg hp.le, ← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); rw [← prod_const v (s:=X),← prod_mul_distrib]; apply Finset.prod_le_prod; exact fun _ _=>mul_nonneg (purse_pos _ _ _ hr _).le hp.le
    exact fun i _=> (show purseX o d θ i*v=purseX o d (θ*v) i from (by unfold purseX; ring)).le.trans (show purseX o d (θ*v) i≤_ from mul_le_mul_of_nonneg_right hξ (by positivity) )
end Girdle
end Plans
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Plans.Girdle.living
