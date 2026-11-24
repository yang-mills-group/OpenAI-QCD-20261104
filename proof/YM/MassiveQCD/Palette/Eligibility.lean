import YM.MassiveQCD.Palette.Shapes
import YM.MassiveQCD.Column.Transmission
/-! # Thin null directions at τX for marker shutters -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew.Phased
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Brick Dust Reggae
open Revolve AnalyticBridge.VerifiedReset PhysicalNext.JointLoad
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f : Side} {N n:ℕ}{X:Support f}(o:Site f){p:BudgetPoint}{v s:ℝ}
local notation "Ω"=> EvenA f N
lemma locales {A:Ω} (h:AccentFit A) (B:SampleX)(i j:Note N):flowN o (grasp A.val) i j B= if i.2=j.2 then locQ o B (feeF i.2 A) i.1 j.1 else 0:=by
   unfold flowN; simp only [signN]; rw [phases A h]; by_cases he:i.2=j.2
   · rw [if_pos he]; unfold locQ; simp_rw [Matrix.sum_apply]; refine sum_congr rfl fun x _=>sum_congr rfl (fun y _=>?_)
     rw [Matrix.blockDiagonal_apply,if_pos (show (placeQ x i).2=(placeQ y j).2 from he), Matrix.smul_apply]; unfold cell; change _* (_* _)=(shine o x* shine o y*_) * _; simp [placeQ]; ring
   rw [if_neg he]; apply sum_eq_zero; intro x _; apply sum_eq_zero; intro y _; rw [Matrix.blockDiagonal_apply,if_neg (show ¬ (placeQ x i).2=(placeQ y j).2 from he), mul_zero,mul_zero]
lemma decbr (A: Grid f→ Ω)(hp:AccentFit (A 1))(hv:shadeG A)(b:Flavor N)(p:SampleX)(ht:Stew.shape o (feeF b (A 1)) p=0) : locQ o p (feeF b (A 1))=0:=by
    let M:= A 1; have he(i j): cell (feeF b M) i j=Stew.goldW (Stew.gold (cell (feeF b M) i j)):= known A hv hp b i j
    have hx:locQ o p (feeF b M)=Stew.goldW (shape o (feeF b M) p):=by unfold locQ Stew.shape; simp_rw [map_sum,map_smul]; refine sum_congr rfl fun i _=>sum_congr rfl (fun j _=>?_) ; rw [← he]
    exact hx.trans (ht ▸ Stew.goldW.map_zero) -- check transport
lemma admit (A:Grid f→Ω)(hp :AccentFit (A 1))(hv:shadeG A) (ht:∀ b,shape o (feeF b (A 1)) none=0): lights o false (grasp (A 1).val):= by
    refine fun x y=>⟨?_,fun h=>Bool.noConfusion h⟩; rw [locales o hp,decbr o A hp hv x.2 none (ht x.2)]; exact ite_self _
lemma shape_exit (A:Grid f→Ω)(hp :AccentFit (A 1))(hv:shadeG A) (hb:mud (A 1)=0)(ht:∀ b,shape o (feeF b (A 1)) none=0): VanishAt o (octave (A 1)):=by
    have hh: Reggae.river f N (A 1)=0:=by change -(mud _).re=0; rw [hb]; simp
    rw [octave,hh,map_zero,sub_zero]; exact ⟨rank_two _ hp,admit o A hp hv ht⟩
lemma eligible {z:Bool} {A:Grid f→Ω} (h:Woven o X p v A s)(hp:AccentFit (A 1))(hv:shadeG A) (hU:0 ≤ v)(hA:o∈X)
    (hy:∀ x,Regal f N (A x)=A x)(hb:mud (A 1)=0)(ht:z→∀ b,shape o (feeF b (A 1)) none=0): Dust.Temper p X o z A v s := by
    refine ⟨h,hv,hy,fun hx=> shape_exit o A hp hv hb (ht hx), (spores o X _ h hv hU).1,hA, (?_ : Reggae.river f N (A 1)=0)⟩
    change -(mud (A 1)).re=0; rw [hb]; simp
variable {b:Flavor N}
lemma repass {z:Bool}{A:Grid f→Ω} (hp:Dust.Feast p X o b A v s) (h:0 ≤ v): Dust.Temper p X o z A v s:= by
     refine eligible o hp.wine (AccentFit.of_fit (hp.art _)) hp.view h hp.base.site hp.joy ?_ fun _ i=>?_ 
     · have hv: Reggae.river f N (A 1)=0:=hp.base.value; rw [show mud _=_ from realP (hp.joy 1),hv]; simp
     have he(b':Flavor N): grasp (A (1:Grid f)).val=copies N (feeF b' (A 1)):=legal (A 1) (hp.art _) b'
     have hv : feeF i (A 1)=feeF b (A 1):=by
        ext x y; change (grasp _) (x,i) (y,i)=_; rw [he b]; exact Matrix.blockDiagonal_apply_eq _ ..
     rw [hv]; exact hp.rack none
end YM.QCD.Stew.Phased
