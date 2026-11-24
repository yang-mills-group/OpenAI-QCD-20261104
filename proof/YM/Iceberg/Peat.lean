import YM.Iceberg.Lilt
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Iceberg
open Function Set Filter Analysis MeasureTheory Lattice
open Massive Massive.UV Massive.Tarn Massive.Tarn.Choir Massive.Tarn.Choir.Strip Massive.Patria.Gall.Onyx
open Massive.Tarn.ChargeQ Massive.Poised.Plans.Stamp.Stair QCD QCD.Lat Massive.Gust
open scoped Topology ContDiff BigOperators Classical ComplexOrder Matrix
open Sprig Intag.Sprig UV.Free Massive.Poised.Plans.Stamp
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K} {ε β:ℝ}{φ:ℕ→ℕ}
variable (hp:C.Path β ε)(hP:P.System)(hHQ:K.Harmony P φ)(ht:Tendsto φ atTop atTop)(hf:Foil P K T)
variable (V:Face→K.W)(hv:Tense T V)(E:Canopy P φ K) (X:Lanterns T E)
open Lanterns Tawny Tawny.Cast Perla Carnal Drill
open Finset TableT Rays Perla.Fore
variable (r u:Flavor 6→ℂ)(p q:ℂ)(a b i:Axis)
noncomputable def Flute(p:ℂ):Fin 4→ℂ:=![0,p,0,-(1/4)*p]
noncomputable def Sette(r:Flavor 6→ℂ)(f:Flavor 6):Fin 4→ℂ:=![0,r f/4,0,0]
lemma spin2 : ∀ v:Flavor 6,axisσ v (Sette r v) = r v • ((1/4:ℂ) • sunS v):=by
    intro v; unfold axisσ Sette; simp; module
lemma pearl : poseσ (Sette r, Flute p)=Hail.flood p r:=by
    have h:gaugeσ (Flute p)=p • solid:=by unfold gaugeσ Flute solid; simp <;> module
    unfold poseσ Hail.flood; change poseσT _ + _=_; rw [h]; unfold poseσT; simp_rw[spin2 r]; rw[add_comm]
lemma violet : star (Flute p)=Flute (star p):=by
    funext i; unfold Flute; fin_cases i<;> first| rfl| simp
lemma rurs : star (Sette r)=Sette (star r):=by
    funext i j; unfold Sette; fin_cases j <;> first| rfl| simp
lemma shrubs (s:RawSym): s.adj 8 a ((Hail.flood p r).val (b,i))=((signT (Signed.mirror a) b:ℂ)*(signT (Signed.mirror a) i:ℂ)) • ((Hail.flood (star p) (star r)).val (b,i)) :=by
    rw [←pearl,spinTurn,rurs,violet,pearl] -- dictionary arguments?
lemma bent: Hail.flood p r= Heron.bendP (fun i:Heron.IceT=>i.elim (-p) (fun v=> -(r v))):=by
    unfold Hail.flood Heron.bendP; rw[Fintype.sum_option]; congr 1
    · change p • solid = (-p) • (-solid); rw[neg_smul, smul_neg, neg_neg]
    apply sum_congr rfl; intro i _; change r i • _= (-(r i)) • (-(1/4:ℂ) • sunS i); rw[neg_smul,neg_smul,smul_neg,neg_neg]
lemma pinsW (h:Hail.shore p r= Hail.shore q u): p=q ∧ r=u:=by
      unfold Hail.shore at h; rw [←pearl,←pearl] at h; let P' :Values 4:=Sette r; let Q:Values 4:=Sette u; have ht: quoS ((P',Flute p)-(Q,Flute q))=0:=by rw[_root_.map_sub,sub_eq_zero]; exact h
      obtain ⟨hr,hv⟩:= (omegaS (P'-Q) (Flute p-Flute q)).1 ht; exact ⟨sub_eq_zero.mp (congr_fun hr 1),funext fun i=>(mul_right_cancel₀ (inv_ne_zero (by norm_num : (4:ℂ) ≠0)) (show r i /(4:ℂ)=u i/ (4:ℂ) from sub_eq_zero.mp ((hv i).2.1)))⟩ -- div is not defeq ?
end YM.Iceberg
#print axioms YM.Iceberg.shrubs
#print axioms YM.Iceberg.bent
#print axioms YM.Iceberg.pinsW
