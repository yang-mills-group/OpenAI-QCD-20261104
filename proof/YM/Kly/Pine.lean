import YM.Kly.Palm
import YM.Sunda.Vermil
set_option maxHeartbeats 540000
set_option autoImplicit false
noncomputable section
namespace YM.Mako
open Set Function Filter Analysis Lattice QCD QCD.Lat
open Massive Massive.UV Massive.UV.Free Massive.Gust Massive.Tarn Massive.Tarn.Choir
open Massive.Patria.Gall Massive.Patria.Gall.Onyx Massive.Tarn.ChargeQ
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder InnerProductSpace
open Heron Iceberg Intag.Sprig Sprig Vern MassiveTwoEstimates Mako
open scoped YM.Iceberg
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K} {W:Axis× Axis→ K.W}{A:Axle K (fun a b=>W (a,b))}{φ:ℕ→ℕ}
variable {E:Canopy P φ K}{X:Lanterns T E}{I:ℕ→ℕ}(J:Glacier T E X W A I)(H:Foil P K T)(JQ:K.Harmony P φ)(B:Vane A)(R:Roof P.sym)
variable {ρ:EuPin→* (K.W≃ₗ[ℂ]K.W)}(S:Steps (A:=A) T R ρ)
set_option quotPrecheck false
local notation "X0"=> equip T ρ A.jet
open Sunda Lobo
open Massive.Bridge.Kly
variable (j:SpaceAxis)
local notation "b"=> Fin.castSucc j
local notation "s₀"=>Maxwell.Free.Corners.quarter timeAxis b
local notation "a"=>timeAxis
local notation "Q"=>Massive.Bridge.Spinor.Lift.daylight j (Real.pi/2)
include j
lemma sawS : (Q).Lifts s₀:= ((Massive.Bridge.Spinor.Lift.way j).2.2 _).trans (Maxwell.Free.Corners.sendsTime _ _ (Ne.symm (Fin.castSucc_ne_last j))).symm -- ordering
lemma tope (x:E4) : (Q).coord.move x a=x b:=by rw [show (Q).coord=(s₀).ortho from sawS j]; simp [Signed.ortho_move,Maxwell.Free.Corners.quarter,Signed.act,Fin.castSucc_ne_last j]
lemma tp_a : (Q).coord.move (basis b)= basis a:=by rw [show (Q).coord=(s₀).ortho from sawS j, Work.A01.move_basis]; simp [Work.A01.eps,Maxwell.Free.Corners.quarter,Signed.matrix_at,Fin.castSucc_ne_last j]
omit j
lemma boundQ(s:Signed)(x y:E4) : cubedist (s.ortho.move x) (s.ortho.move y)=cubedist x y:=by
     have ht (s:Signed)(x y:E4):cubedist (s.ortho.move x) (s.ortho.move y)≤ cubedist x y:=by
             unfold cubedist; apply (dist_pi_le_iff dist_nonneg).2; intro i; obtain ⟨j,h⟩:=s.perm.surjective i; subst i; have he:= dist_le_pi_dist x.ofLp y.ofLp j; rw[Real.dist_eq]; simp only [Signed.ortho_move]; unfold Signed.act; simp only [WithLp.ofLp_toLp,Equiv.symm_apply_apply]; cases hs:s.flip j <;> simp [hs]; -- inspect
             all_goals first|exact (Real.dist_eq .. ▸ he)| (rw [show -x j + y j= -(x j-y j) from by abel,abs_neg]; exact Real.dist_eq .. ▸ he) -- neg add swap
     refine le_antisymm (ht s ..) ?_; have hp:= ht s⁻¹ (s.ortho.move x) (s.ortho.move y); rw [show (s⁻¹).ortho=s.ortho⁻¹ from map_inv Signed.inclusionO s, Ortho.inv_move,Ortho.inv_move] at hp; exact hp
include JQ S R J H B
include j
lemma purity: EuPin.IsRotation Q:=ingens _ (memG j _)
lemma vitalJ (x:K.W): T.adj a (ρ Q x)=ρ Q (T.adj b x):=by
      let C:=Ch T a; have Hq := sawS j; let A:=Q; have hp: Oriole.conjug A g5=g5:=by rw[Sunda.violet,show orient A=1 from (show A.IsRotation from purity J H JQ B R S j), Complex.ofReal_one,one_smul] -- order
      have hh: A.matrix.val*g5=g5*A.matrix.val:=by unfold Oriole.conjug at hp; nth_rw 2 [← hp]; simp only[mul_assoc,show A.matrix⁻¹.val*A.matrix.val=1 from A.matrix.inv_val]; rw [mul_one] -- wrong replaces lhs both
      have hc(w:K.W): C (T.spin A w)= T.spin A (C w):=by
             obtain ⟨d,v,rfl⟩:= JQ.h.absorbs w; change T.spin _ (T.adj _ _) = T.spin _ (T.spin _ (T.adj _ _)); rw [T.w _ _ Hq,T.a,T.a,T.w _ _ (couture a),T.w _ _ (couture a),T.w _ _ Hq]; refine congr_arg (K.focus none _) (Subtype.ext ?_); simp only[RawSym.pinActs,RawSym.adjActs]; rw[rooted _ _ (couture a) (weave a),rooted _ _ (couture a) (weave a)]; exact rotateC Q false (hh.trans (one_smul ℂ _).symm) _
      have hz:A*flipC b=flipC a*A:=by
            apply Subtype.ext; apply Prod.ext
            · apply Ortho.ext; intro x
              have he (i:Axis)(v:E4): (flipC i).coord.move v=v-(2*v i) • basis i:=by rw[show (flipC i).coord=Signed.reflect i from couture i]; ext l; by_cases h:l=i<;> simp [Signed.mirrored,h]; ring -- norm
              change (A.coord*(flipC b).coord).move x=((flipC a).coord*A.coord).move x; rw [Ortho.move_mul, Ortho.move_mul,he,he]; change A.coord.motion (_)=_; rw[map_sub,map_smul,show A.coord.motion (basis b)= _ from tp_a j,tope j]; rfl
            apply Units.ext; let F:= A.matrix.val; change F* (flipC _).matrix.val= (flipC _).matrix.val*F; rw [weave,weave,mul_smul_comm,smul_mul_assoc,←mul_assoc,show F*gamma b= _ from (?_ : F*gamma b = gamma a*F), mul_assoc, mul_assoc,hh]; unfold F; rw [A.act_gamma (j.castSucc),tp_a]; unfold Massive.slash; simp[ite_smul]
      have he:=S.acts JQ.h (loans J H JQ B R); rw[←steal T JQ.h a,← steal T JQ.h b, he A (Maxwell.Free.Corners.quarter ..) Hq,← candles T JQ.h a b,show Ch T a (T.spin A x)= _ from hc x,← he A _ Hq, ← he _ _ (couture a), ← he _ _ (couture b),← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← map_mul,← map_mul]; rw [hz]
omit j
lemma pathways (i:Axis): ∃ p:EuPin,Leads (equip T ρ A.jet) i p:=by
     rcases Fin.eq_castSucc_or_eq_last i with ⟨j,rfl⟩|rfl; · refine ⟨_,purity J H JQ B R S j,tope j,tp_a j,?_,fun x=>(vitalJ J H JQ B R S j x).symm⟩; intro x y; rw [show _ = (Maxwell.Free.Corners.quarter ..).ortho from sawS j]; exact boundQ _ x y
     exact ⟨1,(show older (1: Ortho)=1 from older_one), fun x=> by rw [show EuPin.coord 1=1 from rfl,Ortho.move_one], Ortho.move_one _,fun x y=>by rw [show EuPin.coord 1=1 from rfl,Ortho.move_one, Ortho.move_one], fun x=>by rw[map_one]; rfl⟩
end YM.Mako
#print axioms YM.Mako.pathways
