import YM.QCD.Globe.Pilar
import YM.QCD.Nola.Wheat
import YM.QCD.Nola.Arch
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Globe
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr Kites
variable {f c:Side}{j k m N:ℕ}{S:Flight j k} {h:f.val=c.val*S.L.val}{p:BudgetPoint}
open Fork
variable {X:Sheet c}
def kran (t:SampleX)(u:Cover):ℂ:= t.elim 1 (fun q=> if q.2 then ((2:ℂ)⁻¹)* (u q.1:ℂ) else -((2:ℂ)⁻¹* (u q.1:ℂ)))
lemma kran_spin (i:SampleX)(s:Signed)(u:Cover): kran (Stew.tide s i) (s.act u)=skySig s i * kran i u:=by
    cases i <;> [simp [Stew.tide,kran,skySig]; skip]
    next i=> rcases i with ⟨a,_|_⟩ <;> simp only [kran,Stew.tide,Equiv.optionCongr_apply,Equiv.prodCongr_apply,Option.map_some,Option.elim_some,Prod.map,Bool.false_eq_true,Equiv.refl_apply,↓reduceIte,Signed.act_at,skySig] <;> split <;> simp_all
lemma kran_zero (i:SampleX)(u:Cover):star (kran i u)=kran i u:=by unfold kran; cases i with
    | none=> simp
    | some i=> rcases i with ⟨i,_|_⟩ <;> simp [mul_comm]
def nectar (X:Sheet c)(o:Site c)(i:SampleX): Spike:= (Fintype.card Signed:ℂ)⁻¹ • ∑ j: Site c, ∑ s:Signed, kran i (foam s j) • onSet X o (foam s j)
lemma nectar_fix (h:Tempo X)(o:Site c): nectar X o=nectar X 0:=by funext i; simp only [nectar, h.stillG o]
def allF : Signed:= ⟨Equiv.refl _,fun _=>true⟩
lemma allflip {A:Type*}[AddCommGroup A](x : Four A): allF.act x= - x:=rfl
lemma kran_val (u:Cover)(i:SampleX): kran i u=kran (invert i) (-u):=by cases i with
    | none=> rfl
    | some i=> rcases i with ⟨i,_|_⟩ <;> simp [kran,invert]
lemma sights (hp: Tempo X) : Poem (nectar X 0):=by
    refine ⟨fun p s k h=>?_,fun p=>?_⟩
    · let u:Strut c:=(s,0); obtain ⟨d,hd⟩:= shades s (0:Site c) 0 0; have he:Warrant u d k:=⟨hd,h⟩
      unfold nectar; rw [← Equiv.sum_comp s.actEquiv.toEquiv _]; simp only [Matrix.mul_smul,Matrix.smul_mul]; rw [smul_comm]; congr 1; simp only [Matrix.sum_mul, Matrix.mul_sum, Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _
      let π:=Equiv.mulRight s
      have hπ:= Equiv.sum_comp π (fun v:Signed=>skySig s p • (k*(kran p (foam v i) • onSet X 0 (foam v i))*star k)); change _= ∑ t,_; rw [← hπ]; apply sum_congr rfl; intro t _; change kran (Stew.tide s p) (foam t (s.act i)) • onSet X 0 (foam t (s.act i))=_; rw [assays i s t, kran_spin]
      have hr: onSet X 0 (s.act (foam (t*s) i))= k * onSet X 0 (foam (t*s) i)* star k:=by have he':=hp.visit 0 (foam (t*s) i) u k d he; rw [show act u 0=0 from ?_] at he'; exact he'; change affine s 0 (0:Site c)=_; simp [affine]
      rw [hr,Matrix.mul_smul, Matrix.smul_mul, smul_smul]; rfl -- rev
    unfold nectar; rw [star_smul,star_sum,Matrix.mul_smul,Matrix.smul_mul, star_inv₀, star_natCast]; congr 1; simp only [Matrix.sum_mul,Matrix.mul_sum,star_sum]; rw [← Equiv.sum_comp (Equiv.neg (Site c)) _]; apply sum_congr rfl; intro i _
    let π:=Equiv.mulRight allF
    have hπ:=Equiv.sum_comp π (fun v:Signed=>g5* star (kran p (foam v i) • onSet X 0 (foam v i))*g5);
    rw [← hπ]; apply sum_congr rfl; intro t _; change kran (invert p) (foam t (allF.act i)) • onSet X 0 (foam t (allF.act i))=_; rw [assays,allflip,← kran_val,star_smul,kran_zero, Matrix.mul_smul,Matrix.smul_mul]; exact congr_arg (kran p (foam (t*allF) i) • ·) ((hp.rime _ (-(foam (t*allF) i))).trans (by rw [neg_neg]; rfl))
-- actual wave and mass real.Means
noncomputable def mass (X:Sheet c):ℝ:= qMass (nectar X 0)
noncomputable def sheen (X:Sheet c):ℝ:= qWave (nectar X 0)
lemma Tempo.glitter (hp:Tempo X)(o:Site c)(i:Axis): nectar X o none=(mass X:ℂ) • (1:Spike) ∧ nectar X o (some (i,true))-nectar X o (some (i,false))=(sheen X:ℂ) • Lat.gamma i:=by
    let P:= sights hp -- typo
    rw [nectar_fix hp o]; exact ⟨muse P, by rw [waves P,waves P,← sub_smul,reality P]; rfl⟩
end YM.QCD.Globe
