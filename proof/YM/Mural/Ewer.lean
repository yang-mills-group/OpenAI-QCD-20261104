import YM.Mural.Chisel
import YM.QCD.Jets.Avenue
import YM.MassiveQCD.Stitch.Mint
/-! # Spin degree and output-capped tariff. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Mural
open Function MeasureTheory Finset NormedSpace Creek Creek.Ledge Grass Matrix Cove Anomaly Filter
open scoped Topology BigOperators ContDiff Classical
variable {A B D:Type*}[Fintype A][Fintype B]
def Mild (T:Alg A →L[ℂ] Alg B) := ∀ i:ℕ,∀ x:Alg A,x∈Rim univ i→T x∈ Rim univ i
lemma clipTwo (a b:A): Mild (Creek.v a *Creek.v b):= fun i _ h=> Rim.monotone (Subset.refl _) (by omega) (Rim.clip a (Rim.clip b h))
lemma smear (a b:A): Mild (Creek.l a *Creek.v b):=by
   intro i x h; change atom a * (Creek.v b x)∈ _; cases i; case zero=> rw [Rim.vacated b h,mul_zero]; exact Submodule.zero_mem _
   case succ i=>
      have ht:=Rim.multiply (Rim.atoms (mem_univ a)) (Rim.clip b h); exact Rim.monotone (Subset.refl _) (by omega) ht
lemma mildX (X:Finset D)(f:D→EndA A)(h:∀ i∈X,Mild (f i)): Mild (∑ i∈X,f i):=by intro j a hv; rw [ContinuousLinearMap.sum_apply]; exact Submodule.sum_mem _ fun i hi=>h i hi _ _ hv
lemma mildS (m:ℂ)(x:EndA A)(h:Mild x) : Mild (m • x):=fun n i hi=>Submodule.smul_mem _ _ (h n i hi)
lemma mildB (x y:EndA A)(h:Mild x)(g:Mild y): Mild (x*y):=fun n i hi=> show x (y i)∈_ from h n _ (g n i hi)
lemma mildE (x:EndA A)(h:Mild x): Mild (excess x):=by
   intro n u hu; have hh i: (x^i:EndA A) u∈ Rim univ n:=by induction i with
                 | zero=> simpa using hu
                 | succ i ih=> rw [pow_succ',ContinuousLinearMap.mul_apply]; exact h n _ ih
   let E:=Rim (univ:Finset A) n; apply Submodule.sub_mem _ _ hu; have hf:=E.closed_of_finiteDimensional
   refine hf.mem_of_tendsto (x:=birth x u) (Stays.birther x u) (Eventually.of_forall fun i:Finset ℕ=> Submodule.sum_mem _ fun j _=> ?_); exact (E.smul_mem ((j.factorial:ℂ)⁻¹) (hh j))
lemma collectP (X:Finset D)(f:D→EndA A)(hp:(X:Set _).Pairwise fun i j=>Commute (f i) (f j))(h:∀ i∈ X,Mild (f i)) : Mild (X.noncommProd f hp):=by
   induction X using Finset.induction_on with
   | empty=> exact show Mild (1:EndA A) from fun _ _ h=> by simpa using h
   | insert i X hi ih=> rw [noncommProd_insert_of_notMem X i f hp hi]; exact mildB _ _ (h i (mem_insert_self ..)) (ih _ fun j hj=>h j (mem_insert_of_mem hj))
lemma portV (T:Alg A→ₐ[ℂ] Alg B)(h:∀ a,T (atom a)∈ Rim univ 1): Mild (T.toLinearMap.toContinuousLinearMap):=by
   have hp(L:List A): T (L.map atom).prod∈Rim univ L.length:=by
       induction L with
       | nil=> simp only [List.map_nil,List.prod_nil,map_one]; exact Rim.one _
       | cons a L ih=> rw [List.map_cons,List.prod_cons,map_mul]; exact Rim.monotone (Subset.refl _) (by simp [add_comm]) (Rim.multiply (h _) ih)
   intro i x hx; change T x∈_; rw [Rim.record hx,map_sum]; refine Submodule.sum_mem _ fun j hj=>?_ ; obtain ⟨f,-,hf,hf0⟩:=expression j
   rw [map_smul,hf0]; refine Submodule.smul_mem _ _ ?_; let L:=List.ofFn f; have hv:= hp L; unfold L at hv; rw [List.length_ofFn] at hv -- `expression` domain from index? inspect
   apply Rim.monotone (Subset.refl _) (mem_filter.mp hj).2; convert! hv; simp [L]
open RG Lattice Wilson QCD.Jets Kit Lat YM.Next.Free
variable {E J:Type}{c f:Side}{i j k m n N l:ℕ}{P:Flight i j}{h:f.val=c.val*P.L.val}{η μ t q w:ℝ} {F:Grid f→Sheet f}
variable (X:Sun P c f h η μ q t w l F) (N k)
local notation "T" => X.equip N k
local notation "Q" => Junta c f N
local notation "A" => Modes f N
local notation "B" => Modes c N
lemma temperP (i:Tr f)(U:Grid f): Mild (Cove.bucks T i U):=by
    change Mild (excess ((X.equip N k).treats i U)); refine mildE _ ?_; rcases i with i|i
    · change Mild (pond _ _); unfold pond; refine mildX _ _ fun i _=> mildX _ _ fun j _=> mildS _ _ (clipTwo _ _)
    change Mild (bark _); unfold bark barkG; refine mildX _ _ fun i _=> mildX _ _ fun j _=> mildS _ _ (smear _ _)
open MassiveQCD.Stitch
#check temperP
set_option maxHeartbeats 600000 in
lemma banked (s:Finset (Fj (Tr f) E J))(U:Grid f): Mild (Tablet.tunnel T s U):=by
   have hp:Mild (near A B).toLinearMap.toContinuousLinearMap:= portV _ (fun i=>by erw [embed_atom]; exact Rim.atoms (mem_univ _))
   have hx:Mild (wipe A B ((X.equip N k).shortP U)).toLinearMap.toContinuousLinearMap:= portV _ (fun i=>by
       rcases splits_index i with ⟨i,rfl⟩|⟨i,rfl⟩; rw [wiper]; exact Submodule.sum_mem _ fun j _=> Submodule.smul_mem _ _ (Rim.atoms (mem_univ j)); rw [tails]; exact Rim.atoms (mem_univ _))
   have hg:Mild (axle T U s):= collectP _ _ _ (fun i _=>temperP k N X i U)
   exact fun n i h=> show wipe _ _ _ (axle T U s (near A B i)) ∈ _ from hx n _ (hg _ _ (hp _ _ h))
end YM.QCD.Mural
#print axioms YM.QCD.Mural.banked
