import YM.Mako.Slate
import YM.Mako.Arum
set_option maxHeartbeats 440000
set_option autoImplicit false
noncomputable section
namespace YM.Mako
open Function Filter Set
open Vern Module
open Ortho (plane Skew)
open Org
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius
variable {W:Type*}[AddCommGroup W][Module ℂ W][FiniteDimensional ℂ W]
local notation "M"=> Module.End ℂ W
variable (F:Skew →+ Module.End ℂ W) (hf:∀ x y,clip (F x) (F y)= F (bracket x y))
variable (ht: ∀ (r:ℝ)(p:Skew),F (r • p)=(r:ℂ) • (F p))(hS:∀ i j:Axis,(F (plane i j)).IsSemisimple)
def crowd (f:Pinx→M):Set M:= {themeH f,themeE f,themeF f}
lemma veils (f:Pinx→M) (P:Submodule ℂ M) : crowd f ⊆ P ↔ ∀ i,f i∈P:=by
    constructor <;> intro h
    · let u:= themeH f; let E:=themeE f; let F':=themeF f; have hu: u∈ P:=h (by simp[u,crowd]); have he:E∈ P:= h (by simp[E,crowd]); have hv:F'∈P:=h (by simp [F',crowd]); intro i; fin_cases i
      · change f 0∈P; rw [show f 0=(2*Complex.I:ℂ)⁻¹ • u from (inv_smul_smul₀ (mul_ne_zero (by norm_num) Complex.I_ne_zero) _).symm]; exact P.smul_mem _ hu
      · change f 1∈P; rw[show f 1= (1/2:ℂ) • (E-F') from by unfold E F' themeE themeF; module]; exact P.smul_mem _ (P.sub_mem he hv)
      change f 2∈P; rw[show f 2=(2*Complex.I)⁻¹ • (E+F') from ?_]; exact P.smul_mem _ (P.add_mem he hv)
      rw [show E+F'= (2*Complex.I:ℂ) • f 2 from by unfold E F' themeE themeF; module, inv_smul_smul₀ (mul_ne_zero (by norm_num) Complex.I_ne_zero)]
    intro i hi; rcases (show i=themeH f∨i=themeE f∨i=themeF f from by simpa [crowd] using hi) with rfl|rfl|rfl; · exact P.smul_mem _ (h _)
    · exact P.add_mem (h _) (P.smul_mem _ (h _))
    exact P.neg_mem (P.sub_mem (h _) (P.smul_mem _ (h _)))
lemma codes (f g:Pinx→M)(h:∀ i j:Pinx,Commute (f i) (g j)) (x:M)(hx:x∈crowd f)(y:M)(hy:y∈crowd g): Commute x y:=by
      let L (x:M):Submodule ℂ M:= {
           carrier:={y|Commute x y},zero_mem':=Commute.zero_right _, add_mem':=fun {i j} (p: Commute x i) (q: Commute x j)=> p.add_right q,smul_mem':=fun a _ (p: Commute x _)=> p.smul_right a }
      apply (show crowd g⊆L x from (veils g (L x)).mpr (fun i=> (show Commute (g i) x from ?_).symm)); exact hy -- apply syntax leaves goal order
      exact ((veils f (L (g i))).mpr fun j=> (h j i).symm) hx
lemma soar_one (i:Pinx): groth i= evoke true i+evoke false i :=by simp only[evoke,Bool.false_eq_true,↓reduceIte]; module
lemma soar_two(i:Pinx):retta i= evoke true i - evoke false i:=by simp only [evoke,Bool.false_eq_true,↓reduceIte]; module
lemma sticks (U:Submodule ℝ Skew)(h:∀ b i,evoke b i∈U): U=⊤:=by
     have hz(i):groth i∈U:=by rw [soar_one]; exact U.add_mem (h ..) (h ..)
     have ht(i):retta i∈U:=by rw[soar_two]; exact U.sub_mem (h ..) (h ..)
     let TPx(i j:Axis):Prop:=plane i j∈U
     have ha :TPx 0 1:= ht 0; have hb:TPx 0 2:= ht 1; have hc:TPx 0 3:=ht 2; have he:TPx 2 3:=U.neg_mem_iff.mp (show -plane 2 3∈U from hz 0); have hf:TPx 3 1:=U.neg_mem_iff.mp (show -plane 3 1∈U from hz 1); have hp:TPx 1 2:=U.neg_mem_iff.mp (show -plane 1 2∈U from hz 2)
     have hy(a):TPx a a:=by unfold TPx; rw [show plane a a=0 from Subtype.ext (by simp [plane])]; exact U.zero_mem
     have hq(a b:Axis)(h:TPx b a): TPx a b:=by unfold TPx; rw[swapπ]; exact U.neg_mem h
     have hh(a b):TPx a b:=by fin_cases a<;> fin_cases b<;>first | exact ha|exact hb|exact hc|exact he|exact hf|exact hp|exact hy _|(apply hq; first|exact ha|exact hb|exact hc|exact he|exact hf|exact hp)
     rw[eq_top_iff,← Spin.spans,Submodule.span_le]; rintro v ⟨i,rfl⟩; exact hh i.1 i.2
include ht
lemma soapy :Submodule.span ℂ (crowd (F ∘ evoke false)∪crowd (F ∘ evoke true))= Submodule.span ℂ (Set.range F):=by
      let C:= crowd (F ∘ evoke false)∪crowd (F ∘ evoke true); let U:= Submodule.span ℂ C; let V:=Submodule.span ℂ (range ⇑F); change U=V; have hh(b):crowd (F ∘ evoke b)⊆ V:= (veils _ _).mpr fun i=> Submodule.subset_span ⟨evoke b i,rfl⟩
      let P:Submodule ℝ Skew:= {
           carrier:={x|F x∈U},zero_mem':=by change F 0∈ U; rw[map_zero]; exact U.zero_mem
           add_mem':=fun {p q} hp hq=>by change F (p+q)∈ U; rw[map_add]; exact U.add_mem hp hq
           smul_mem':=fun c p hp=>by change F (c • p)∈ U; rw [ht]; exact U.smul_mem (c:ℂ) hp } -- c real ↑
      have hp : P=⊤:=sticks P (by intro b i; apply (show ∀ j,F (evoke b j)∈U from (veils _ U).1 (show crowd (F ∘ evoke b)⊆ U from ?_)) i; intro x hx; apply Submodule.subset_span; cases b; exact Or.inl hx; exact Or.inr hx)
      refine le_antisymm (Submodule.span_le.mpr (union_subset (hh false) (hh true))) (Submodule.span_le.mpr ?_); rintro v ⟨t,rfl⟩; exact (show t∈P from by rw[hp]; simp)
include hf hS
lemma surges :∃ p:Module.End ℂ W, Split p (Set.range F):=by
      let X(b:Bool): Pinx→M:= F ∘ evoke b
      have hh(b): Links (themeH (X b)) (themeE (X b)) (themeF (X b)):= orate (X b) (fun i=>by unfold X Function.comp; rw[hf,pool])
      choose f h using (fun b=> (hh b).creates (slice _ (co_semisi F hf ht hS b)))
      let C:= crowd (X false); let D:= crowd (X true); refine ⟨f false*f true,?_⟩; exact ((show Split (f false) C from h false).joins _ _ (show Split (f true) D from h true) (codes (X false) (X true) (fun i j=>sub_eq_zero.mp (Eq.trans (hf _ _) (by rw[stripe,map_zero]))))).home _ (soapy F ht)
end YM.Mako
#print axioms YM.Mako.surges
