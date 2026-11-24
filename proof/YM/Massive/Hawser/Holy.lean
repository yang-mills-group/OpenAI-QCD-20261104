import YM.Massive.Hawser.Timber
/-! # Visible labels in free comparator after equation ideal. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.UV.Free
open Lattice Wilson RG Source Function QCD Lat Massive Lining Papyrus Filter Work.G05 Finset Matrix Grass TensorProduct
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators NNReal Classical Kronecker TensorProduct
open Fountain
namespace Harbor
variable {d:ℕ}(a b:Flavor 6)(S:Spike)(i j k:Pinor)
abbrev l (d:ℕ)(x:Hue): Pairs (SpinMode d):=Sum.inl ((0,i,x),a)
abbrev r (d:ℕ)(x:Hue): Pairs (SpinMode d):=Sum.inr ((0,i,x),a)
private abbrev crest (d:ℕ) : Finset (Pairs (SpinMode d)) := {r a i d 0,l b j d 0}
private lemma glow2{X:Type*}[DecidableEq X][Fintype X](i j:X)(h:i≠j) : atom i*atom j≠0:=by simpa using flame [i,j] (by simp [h])
private lemma glow3{X:Type*}[DecidableEq X][Fintype X](i j k:X)(h:i≠j)(hp:i≠k)(hv:j≠k): atom i*atom j*atom k≠0:=by simpa [mul_assoc] using flame [i,j,k] (by simp [h,hp,hv]) -- mul assoc name
lemma floor_c : Floor (crest a b i j d):=by intro l hp; simp only [crest,mem_insert,mem_singleton] at hp; rcases hp with h|h <;> rw [h] <;> rfl
private lemma rewB (x:Pinor)(z:Hue): waveP (crest a b i j d) (other 0 a x z)=if x=i ∧ z=0 then other 0 a i 0 else 0:=by
    unfold other bar; rw [Fountain.carrier]; by_cases hx:x=i <;> by_cases hz:z=0 <;> simp [*,crest,l,r]
private lemma rewL (x:Pinor)(z:Hue): waveP (crest a b i j d) (male 0 b x z)=if x=j ∧ z=0 then male 0 b j 0 else 0:=by
    unfold male Grass.psi; rw [Fountain.carrier]; by_cases hx:x=j <;> by_cases hz:z=0 <;> simp [*,crest,l,r]
lemma absorb (d:ℕ) : waveP (crest a b i j d) (sPair a b S d)=S i j • (other 0 a i 0*male 0 b j 0):=by
    unfold sPair; simp_rw [map_sum,map_smul, map_mul,rewB,rewL]; rw [sum_eq_single i]; rw [sum_eq_single j]; rw [sum_eq_single (0:Hue)]; simp; intro z _ hz; simp [hz]; simp
    · intro p _ hp; simp [hp]
    · simp
    · intro p _ hp; simp [hp]
    simp
lemma meson_visible (h: 6≤d)(he:S≠0) : projection (mesonCode d a b S h)≠0:=by
   obtain ⟨i,j,H⟩:∃ i j,S i j≠0:=by contrapose! he; ext i j; exact he i j
   refine crystal (floor_c a b i j) _ (sPair ..) rfl ?_; rw [absorb]; exact smul_ne_zero H (glow2 (r a i d 0) (l b j d 0) (by simp [l,r])) -- syntax
open Pearl
local notation "V" => Pairs (SpinMode 9)
private abbrev peaks : Finset V:= {l 0 i 9 0,l 1 j 9 1,l 2 k 9 2}
lemma peaksF : Floor (peaks i j k):=by
    intro x hp; simp only [peaks,mem_insert, mem_singleton] at hp; rcases hp with h|h|h <;> rw [h] <;> rfl
private lemma p1 (z:Hue) : waveP (peaks i j k) (isk i z)=if z=0 then isk i 0 else 0:=by unfold isk; change waveP _ (atom (l 0 i 9 z))= _; rw [carrier]; by_cases hh:z=0 <;> simp [*,peaks,l,show (0:Flavor 6)≠2 by decide]
private lemma p2 (z:Hue) : waveP (peaks i j k) (esk j z)=if z=1 then esk j 1 else 0:=by unfold esk; change waveP _ (atom (l 1 j 9 z))= _; rw [carrier]; by_cases hh:z=1 <;> simp [*,peaks,l,show (1:Flavor 6)≠2 by decide]
private lemma p3 (z:Hue) : waveP (peaks i j k) (ots k z)=if z=2 then ots k 2 else 0:=by unfold ots; change waveP _ (atom (l 2 k 9 z))= _; rw [carrier]; by_cases hh:z=2 <;> simp [*,peaks,l,show (2:Flavor 6)≠1 by decide,show (2:Flavor 6)≠0 by decide]
lemma pearl_visible : projection (rock i j k)≠0:=by
    have he (u:Equiv.Perm Hue) (h:u≠1): waveP (peaks i j k) (Pearl.rowW i j k (Pearl.α u))=0:=by
       have H: ¬(u 0=0∧u 1=1∧u 2=2):= by
          intro ht; apply h; ext1 i; fin_cases i <;> first|exact ht.1|exact ht.2.1|exact ht.2.2
       unfold Pearl.rowW Pearl.α; rw [map_mul,map_mul]; simp only [p1,p2,p3]; split_ifs <;> simp_all
    refine crystal (peaksF i j k) _ (lighthouse i j k) (Pearl.τ ..) ?_; unfold lighthouse; rw [map_sum,sum_eq_single (1:Equiv.Perm Hue)]
    · rw [map_smul,Pearl.ε, Equiv.Perm.sign_one]; unfold Pearl.rowW Pearl.α; rw [map_mul,map_mul]; simp only [id_eq, Equiv.Perm.coe_one, p1, p2, p3, if_true,Units.val_one, Int.cast_one,one_smul]; exact glow3 (l 0 i 9 0) (l 1 j 9 1) (l 2 k 9 2) (by simp [l]) (by simp [l,show (0:Flavor 6)≠2 by decide]) (by simp [l,show (1:Flavor 6)≠2 by decide])
    · intro σ _ h; rw [map_smul,he σ h,smul_zero]
    simp
end Harbor
end YM.Massive.UV.Free
#print axioms YM.Massive.UV.Free.Harbor.pearl_visible
#print axioms YM.Massive.UV.Free.Harbor.meson_visible
