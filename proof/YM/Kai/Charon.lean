import YM.Kai.Petal
/-! wreath families: only true scopes, canonical signs. Scale ± on reflection chains. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.PCAC.Oren
open Function Filter MeasureTheory Set QCD QCD.Lat QCD.Grass Lattice Wilson UV RG QCD.Grass.Ward
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator Classical TensorProduct Kronecker
open Poised Poised.Beacon Poised.Plans Finset Module Poised.Stative Massive.Patria Patria.Exposure Depth Intag
open Entr Entr.Meridian Stew Cylinder
open QCD.Tide Revolve Onsite
variable {S:Scheme}{R c:Side}{d n i l j:ℕ}
-- common report. Includes reflection ph. 
structure Slate where
     hop : Bool
     flavor : Flavor 6
     axis:Axis
     z:ℝ
     nng : z*z=1
variable (B:Slate)(p:Site c)
noncomputable def Wagon (a:Slate) (p:Site c) : Stall c 6:= (a.z:ℂ) • (if a.hop then beacon a.flavor p a.axis else zoneD a.flavor p a.axis)
lemma turnout: (B.z:ℂ)≠0:=by intro h; have hc:= Complex.ofReal_eq_zero.mp h; have he:=B.nng; rw [hc,mul_zero] at he; exact zero_ne_one he
lemma twang: ‖(B.z:ℂ)‖=1:=by rw [Complex.norm_real,Real.norm_eq_abs]; nlinarith [B.nng,sq_abs B.z,abs_nonneg B.z]
lemma honest (n m:ℕ):∃ C:ℝ,0≤ C∧ ∀ (h:BudgetPoint)(B:Slate), h.order≤ n → h.power ≤ m → ∀ (c:Side)(p:Site c), Suit p h C (Wagon B p):=by
      obtain ⟨C,hc,H⟩:= chin 6 n m; let v(i:Axis):=veinFare (gamma i)+veinFare (gamma i); let A:= ∑ i:Axis,v i; have hp(i:Axis): 0 ≤ v i:=by unfold v veinFare; positivity
      refine ⟨max (C+C) A,(add_nonneg hc hc).trans (le_max_left ..),fun h B ht hm c p=>?_⟩; suffices hz: Suit p h (max (C+C) A) (if B.hop then beacon B.flavor p B.axis else zoneD B.flavor p B.axis) by
           have hf:= hz.scaleF _ (B.z:ℂ); rwa [twang, one_mul] at hf
      rcases H c h ht hm B.axis p B.flavor with ⟨hC,hK⟩; split; exact (orbitKeel p B.axis B.flavor C hC hK).beyond _ (le_max_left ..)
      exact (orbitA p (gamma B.axis) B.flavor).beyond _ ((single_le_sum (fun i _=> hp i) (mem_univ _)).trans (le_max_right ..)) -- beyond order
-- unwound
lemma evenT : Continuous (Wagon B p):=by
     let h:BudgetPoint:= ⟨2,6,1,2,1,le_rfl,le_rfl,by norm_num,by decide,by norm_num,le_rfl⟩; obtain ⟨C,_,H⟩:=honest h.order h.power; obtain ⟨J,hJ,f,g,w,r,h1,h2,h3⟩:= (H h B le_rfl le_rfl c p).lanes
     rw [funext h3]; exact continuous_finsetSum _ fun i _=>(h2 i).2.2.2.1.smul continuous_const
-- use Move and Reflect independently
variable (a: Axis)(X:Lat.Fields c 6)(g: Signed)(U:Grid c)(N:Spike)(p':Site c)(l:Site c→ℂ)(hG: Glare g (0:Site c) 0 p' l)(hN:Swing g N)
noncomputable def facing (g: Signed):Slate:= {B with axis:=g.perm B.axis}
noncomputable def opposed(a:Axis) : Slate:= { B with z:= signT (Signed.mirror a) B.axis * B.z,nng:= by nlinarith [UV.sign_sq (Signed.mirror a) B.axis,B.nng] } -- product identity nlinarith
local notation "B1"=> Wagon B p
local notation "E"=> shiftE g p' p
local notation "V"=> hues p' g l N
local notation "Q"=> Kit.disguise (copies 6 V)
local notation "T"=> pull g p' U
local notation "K"=> ((signT g B.axis:ℝ):ℂ)
include hN hG
lemma elan : Q (Wagon B p T X)= K • Wagon (facing B g) E U (Q X):=by
    unfold Wagon facing; simp only [Pi.smul_apply,ContinuousLinearMap.smul_apply,map_smul]; split; rw[meek B.flavor p' p g l B.axis N hG U hN, smul_comm]; rw [dry B.flavor p' p g l B.axis N hG U hN,smul_comm]
omit hN hG
lemma echoT : let P:= Patria.Exposure.eyeP c a; let t:=Signed.mirror a; tilt P ((B1) (pull t 0 U) X)=(Wagon (opposed B a) (t.act p) U (tilt P X)) :=by
     intro P t; unfold Wagon opposed; simp only [Pi.smul_apply,ContinuousLinearMap.smul_apply,map_smulₛₗ,Complex.conj_ofReal]; rw [Complex.ofReal_mul]; split
     · rw [show tilt P _= _ from waveRed B.flavor p B.axis a U X,smul_smul, mul_comm (↑B.z :ℂ)] -- arguments order
     rw [show tilt P _= _ from surfT B.flavor p B.axis a U X,smul_smul,mul_comm (↑B.z:ℂ)]
-- cut sample
variable (A:Massive.Run S n R 6)(hA:A.Actual)
noncomputable def inkC (b:Cover): Insertion (S.side R i) 6 := ⟨fun U=> Wagon B (wrap _ b) U (actor A i U), (evenT _ _).clm_apply (actor A i).continuous⟩
include hA
local notation "M"=> S.side R i
local notation "Ξ"=> actor A i
local notation "I"=> inkC (i:=i) B A
open TorusPCAC.Geometry
private lemma moveΞ (t:Cover)(hi:i≤ n) : march t (⇑Ξ)= ⇑Ξ:=by rw [act A hA hi,pier A hA hi]; exact Patria.Depth.first _ _ hi _
lemma stampC (hi:i≤n) (u:Averaging):Patria.Depth.TideT A u i (report A I u):=by
    apply stampF A _ u; intro a b; funext U; let Vα:= Kit.disguise (copies 6 (hues (wrap M b) 1 (heat b) 1)); let G:=pull 1 (wrap M b) U; have hk: Vα (actor A i G) = actor A i U:= congr_fun (moveΞ A hA b hi) U
    let D:= shiftE 1 (wrap M b) (wrap M a); change Vα (Wagon B (wrap M a) G (actor A i G))=_; have h': Vα (Wagon B (wrap M a) G _) = _:= elan B (wrap M a) (actor A i G) 1 U 1 (wrap _ b) (heat b) (TorusPCAC.Geometry.glares b) Revolve.Swing.none -- hp order
    rw [h',hk,show shiftE 1 (wrap M b) (wrap M a)=wrap M (a+b) from (by simp[shiftE,Signed.actEquiv]),show signT 1 B.axis=1 from (by simp[signT]),Complex.ofReal_one,one_smul]; rfl
lemma frolic (b:Cover)(t:Axis)(hi:i≤ n): Cylinder.Action.adj t (⇑(I b))=⇑(inkC (i:=i) (opposed B t) A ((Signed.mirror t).act b)):=by
      have he: Action.adj t (⇑(actor A i))=⇑(actor A i):=by rw[act A hA hi,pier A hA hi]; exact (Patria.Depth.arrives A i hi).2.1 t
      funext U; let P:= Patria.Exposure.eyeP M t; let s:= Signed.mirror t; rw [eye_value]; change tilt P (Wagon B _ _ _)= Wagon (opposed B t) (wrap M (s.act b)) U (actor A i U)
      rw [←congr_fun he U,eye_value,← wrap_signed]; exact echoT B (wrap M b) t _ U
end YM.Massive.PCAC.Oren
#print axioms YM.Massive.PCAC.Oren.frolic
#print axioms YM.Massive.PCAC.Oren.honest
#print axioms YM.Massive.PCAC.Oren.stampC
