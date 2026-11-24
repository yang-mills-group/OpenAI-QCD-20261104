import YM.Portland.Spoon
import YM.Mural.Wince
/-! # LocalPrice integration with same controller Actual. Not required to remember any particular Φ along α hard log (physics from pressure cert). -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC.Brave.CoatB
open QCD QCD.Grass QCD.Lat Lattice Wilson RG Function Filter MeasureTheory QCD.Grass.Ward Grass.Ovule
open YM.Next.Free QCD.Flume QCD.Globe QCD.Globe.HalfMass Finset NormedSpace
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator Classical ComplexOrder
variable {A B:Type*} [Fintype A][Fintype B]
variable {c f R:Side} {n l t s p m i F:ℕ}
variable (a b:Flavor F)
variable {S:Scheme}
local notation "pC"=>Lat.wave
-- B slots locked to initial q operations. use exact tilt on all.V.
variable (L:Flight l t) (h:f.val=c.val*L.L.val) (K:KernelChoices)(r β:ℝ)(hk:L.patch.Branches K su)
open QCD.Comet Push.AbsoluteSums
local notation "Ω"=> Modes c F
local notation "κ"=> Modes f F
lemma shut (E:Deck f F)(hP:Bordered a b E)(i j:Modes c F)(he:¬ (i.2=a ∧ j.2=b)) : Quilt L K h β r hk E i j=0:=by
     unfold Quilt; rw [sum_eq_zero,map_zero]; intro p _; apply ContinuousMap.ext; intro W
     by_cases hv:E p.1 p.2=0; · rw [hv]; exact smul_zero _ -- cw.apply
     have hx:=hP p.1 p.2 hv -- hP direct func
     let Q:= qmove L h F W; have hp(i:Modes c F)(j:Modes f F)(hX:i.2≠j.2): Q i j=0:=by
          change qmove L h F W (idx i.1.1 (i.1.2.1,i.2) i.1.2.2) (idx j.1.1 (j.1.2.1,j.2) j.1.2.2)=0; rw [hingeQ,if_neg ?_]; exact fun h=>hX (Prod.ext_iff.mp h).2
     rcases not_and_or.mp he with hh|hh
     · change (Q i p.1* star (Q j p.2)) • (E p.1 p.2 W)=0; rw [hp i p.1 (hx.1.symm ▸ hh),zero_mul,zero_smul]
     change (Q i p.1* star (Q j p.2)) • (E p.1 p.2 W)=0; rw [hp j p.2 (hx.2.symm ▸ hh),star_zero,mul_zero,zero_smul]
lemma shielded (Z:Spike)(Y:Insertion c F)(E:Deck f F)(H:Bordered a b E) : Bordered a b (toward L K h β r hk (flavorW Z a b c) Y E):=by
     intro i j hx; by_contra hp; apply hx; have h0 : flavorW Z a b c i j=0:=by change _* (if i.2=a ∧ j.2=b then (1:ℂ) else 0)=0; rw [if_neg hp,mul_zero] -- expr
     unfold toward; change (_:ℂ) • ((flavorW Z a b c i j) • Y+Quilt L K h β r hk E i j)=_; rw [h0,zero_smul,zero_add,shut a b L h K r β hk E H i j hp, smul_zero]
variable (T:Run S n R F)(Z X:Spike)
variable (M:∀ i:ℕ, Deck (S.side R i) F) (hc : M p=0) (hp:∀ i<p,M i= liftM T Z a b i (M (i+1)))
include hc hp
lemma shield : ∀ i≤p,Bordered a b (M i):=by
     intro i h; induction h using Nat.decreasingInduction with |self=>rw[hc]; exact fun i j h=>False.elim (h rfl)|of_succ i h ih=>rw [hp i h]; exact shielded a b _ _ _ _ _ _ Z _ _ ih
local notation "Rr"=> S.side R m
variable (V:TokenP)(D:DeckV (S.side R m) F)
variable (ht:T.Actual)(hr:m≤ n)
variable {φ v u w:ℝ}{α:ℂ}
variable (h1:1 ≤ V.t)(h2:1 ≤V.f)(h3:0 ≤ V.e)(h4:0 ≤ V.k)(h5:1 ≤V.w)(h6:0 ≤V.v)
local notation "M0"=> (M m)
local notation "ACT"=> actor T m
variable (hA:actor T m (1:Grid (S.side R m))= α • D.density 1)(hf:Invoice D (M m) i V (actor T m) α u v)
local notation "C1"=>u+v*V.v
local notation "C₂"=>bronze V v 2
local notation "C₄"=>bronze V v 4
variable (he:m ≤ p)
local notation "Ds"=> T.density m
include hA hf h1 h2 h3 h4 h5 h6 ht hr he
lemma spiceQ : Tuned a b i (T.density m 1) C1 C₂ C₄ (M m):=by
     refine ⟨shield a b T Z M hc hp m he, fun x y hx=> ?_,fun x y hx=>?_ ⟩
     · let v':=cargo (M m) x.1.1 y.1.1 (x.1.2.1,x.2) (y.1.2.1,y.2)
       exact congr_fun (show v'=0 from hf.scope x.1.1 y.1.1 hx _ _) (x.1.2.2,y.1.2.2)
     rw [← act T ht hr,hA]; apply birthW D (x.2.2,y.2.2) x.1 y.1 V α h1 h2 h3 h4 h5 h6 (actor T m) hA i _ (x.2.1,a) (y.2.1,b) hf hx -- apply dep.
variable {η θ:ℝ} (K':ℝ)(hv:0≤K')(hx: 0≤u)(hz:0 ≤v)(ha:a≠b)(hE: LocalPrice (T.density m) θ φ)(hΨ:∀ j, ‖T.massRead m j‖≤η)(hM: 2*beamSize φ ≤ amount (S.side R m)*(K'-η))
local notation "Vf"=> cupSize X i K' C1 C₂ C₄ θ
include hM hE hΨ hv hx hz ha
lemma rewarded : ‖chord X a b T m (passenger (M m))‖ ≤ cupSize X i K' C1 C₂ C₄ θ:=by
    obtain ⟨W,z,t,hW,hZ,h0,hK,H,hγ,hΩ⟩:=hE.source; have h:=spiceQ a b T Z M hc hp V D ht hr h1 h2 h3 h4 h5 h6 hA hf he
    have hp' :∀ i j, ‖stalk (t i) j‖ ≤ K':=by
         intro i j; have hm:=stalk_cost (hΩ i).2 (hΩ i).1 j; have he : artPrice 1 (t i)=T.massRead m i:=by rw [H i,art_mul]; rw [show T.massRead m i=_ from Eq.symm (point_cost Ds i),art_horn]
         rw[he] at hm; have hX:0< amount (S.side R m):= Nat.cast_pos.mpr (S.side R m).pos
         apply le_of_mul_le_mul_left _ hX; nlinarith only [hM,hm, mul_le_mul_of_nonneg_left (hΨ i) hX.le]
    have hv:(u+v*V.v)≥0:=add_nonneg hx (mul_nonneg hz h6); have hm(n):0≤bronze V v n:=by unfold bronze; exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (mul_nonneg hz h6) (pow_nonneg (mul_nonneg (zero_le_one.trans h1) (zero_le_one.trans h2)) _))
    rw [hW] at h; unfold chord Stiffness.body; rw [hW,map_smul,smul_eq_mul]; let μ:= Ovule.core (Cove.Keys (S.side R m) F); have hO: z * μ (exp W.val)≠0:=by rw [show μ (exp W.val)=_ from (?_: μ (exp W.val)=1),mul_one]; exact hZ; exact Loft.body_exp (panel_body W.val h0)
    exact cupTop a b X W.val t ha hK z K' C1 C₂ C₄ W.property hO ‹0≤K'› hv (hm 2) (hm 4) (hΩ a).1 hp' i _ h θ hγ
end YM.Massive.PCAC.Brave.CoatB
#print axioms YM.Massive.PCAC.Brave.CoatB.rewarded
