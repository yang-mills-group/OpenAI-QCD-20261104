import YM.Massive.PCAC.Mark
import YM.Massive.RG.Motion
/-! Passage and partial pass calculus on the joint field algebra. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Grass.Ward
open Function Finset Module NormedSpace
open scoped BigOperators Topology Matrix Classical
variable {A B C:Type*}[Fintype A][Fintype B][Fintype C]
lemma mark_one (k:Bool)(W:Sour A): applyMark k W (1:Dirac A)=0:=by cases k <;> simp [applyMark,gen_one]
lemma through_mark {k l:Bool}{U:Sour A}{V:Sour B}(f:Dirac A→ₐ[ℂ]Dirac B)(h:∀ i:Pairs A, applyMark l V (f (atom i))= f (applyMark k U (atom i)))(x:Dirac A) : applyMark l V (f x)= f (applyMark k U x):=by
    have he (m:List (Pairs A)): applyMark l V (f (m.map atom).prod) = f (applyMark k U (m.map atom).prod):=by
        induction m with
        | nil=> simp [mark_one]
        | cons i m ih=> simp only [List.map_cons,List.prod_cons,LMark,map_mul,map_add,h,ih] -- simpl order LMark before
    have hp (s:Finset (Pairs A)): applyMark l V (f (mono s))= f (applyMark k U (mono s)):=by obtain ⟨u,h',hv,hx⟩:=expression s; rw [hx]; simpa only [List.map_ofFn] using he (List.ofFn u)
    rw [←write x]; simp only [map_sum,map_smul,hp]
def jointChoice (U:Sour A)(V:Sour B): Sour (A⊕B):= Matrix.fromBlocks U 0 0 V
lemma markNear (k:Bool)(U:Sour A)(V:Sour B)(x:Dirac A) : applyMark k (jointChoice U V) (near A B x)=near A B (applyMark k U x):=by
   apply through_mark; rintro (i|i)
   · change applyMark k _ (pass _ (psi i))= pass _ (applyMark k U (psi i)); rw [pass_psi]; cases k
     · rw [leftP,leftP]; simp [Fintype.sum_sum_type,jointChoice, pass_psi]
     simp [passP]
   change applyMark k _ (pass _ (bar i))= pass _ (applyMark k U (bar i)); rw [pass_bar]; cases k
   · simp [passB]
   rw [leftB,leftB]; simp [Fintype.sum_sum_type,jointChoice,pass_bar]
lemma markFar (k:Bool)(U:Sour A)(V:Sour B)(x:Dirac B) : applyMark k (jointChoice U V) (far A B x)=far A B (applyMark k V x):=by
   apply through_mark; rintro (i|i)
   · change applyMark k _ (pass _ (psi i))= pass _ (applyMark k V (psi i)); rw [pass_psi]; cases k
     · rw [leftP,leftP]; simp [Fintype.sum_sum_type,jointChoice, pass_psi]
     simp [passP]
   change applyMark k _ (pass _ (bar i))= pass _ (applyMark k V (bar i)); rw [pass_bar]; cases k
   · simp [passB]
   rw [leftB,leftB]; simp [Fintype.sum_sum_type,jointChoice,pass_bar]
lemma passthrough {E:Type*}[AddCommGroup E][Module ℂ E](Z T:Dirac (A⊕B)→ₗ[ℂ]E) (h: ∀ x:Dirac A,∀ y:Dirac B,Z (near A B x*far A B y)=T (near A B x*far A B y)) : Z=T:=LinearMap.ext fun x=>by
    rw [←write x]; have he (s:Finset (Pairs (A⊕B))): Z (mono s)=T (mono s):=by obtain ⟨i,j,hv|hv⟩:= split_mono A B s <;> simp [hv,h];
    simp [he]
lemma marginal_mark (k:Bool)(U:Sour A)(V:Sour B)(x:Dirac (A⊕B))(h:U.trace=0): marginal A B (applyMark k (jointChoice U V) x)= applyMark k V (marginal A B x):=by
    refine LinearMap.congr_fun (passthrough (A:=A) (B:=B) ((marginal A B).comp (applyMark k (jointChoice U V))) ((applyMark k V).comp (marginal A B)) ?_) x; intro u v; rw [LinearMap.comp_apply,LinearMap.comp_apply,LMark,markNear,markFar,map_add,margins,margins,margins,integrated,h,zero_mul,map_smul]; simp

-- Left derivative slots on margin.Mind parity!
abbrev beforeK (B:Type*) : Pairs A→Pairs (A⊕B) := Sum.map Sum.inl Sum.inl
abbrev besideK (A:Type*) : Pairs B→Pairs (A⊕B) := Sum.map Sum.inr Sum.inr
lemma near_d (i:Pairs A)(x:Dirac A): vary (beforeK B i) (near A B x)= near A B (vary i x):= survives (f:=beforeK B) (Sum.map_injective.mpr ⟨Sum.inl_injective,Sum.inl_injective⟩) i x
lemma far_d (i:Pairs B)(x:Dirac B): vary (besideK A i) (far A B x)= far A B (vary i x):= survives (f:=besideK A) (Sum.map_injective.mpr ⟨Sum.inr_injective,Sum.inr_injective⟩) i x
lemma vary_ignores {f:A→B}(i:B)(h:∀ j:A,i≠f j)(x:Alg A) : vary i (embed f x)=0:=by
    have he(l:List A): vary i (embed f (l.map atom).prod)=0:=by
       induction l with
       | nil=> simp [vary_one]
       | cons a l ih=> simp only [List.map_cons,List.prod_cons,map_mul,embed_atom, vary_mul,vary_off i _ (h a),ih,zero_mul,mul_zero,add_zero]
    have hv(s:Finset A):vary i (embed f (mono s))=0:=by obtain ⟨w,-,-,H⟩:= expression s; rw [H]; simpa only [List.map_ofFn] using he (List.ofFn w)
    rw [←write x]; simp only [map_sum,map_smul,hv,smul_zero,sum_const_zero]
lemma ignores_near (i:Pairs B)(x:Dirac A): vary (besideK A i) (near A B x)=0:= vary_ignores (f:=beforeK B) _ (fun j=>by cases i<;>cases j<;>simp [beforeK,besideK]) x
lemma ignores_far (i:Pairs A)(x:Dirac B): vary (beforeK B i) (far A B x)=0:= vary_ignores (f:=besideK A) _ (fun j=>by cases i<;>cases j<;>simp [beforeK,besideK]) x
lemma vanishes (i:Pairs A)(x:Dirac (A⊕B)): marginal A B (vary (beforeK B i) x)=0:=by
    refine LinearMap.congr_fun (passthrough (A:=A) (B:=B) ((marginal A B).comp (vary (beforeK B i))) (0: Dirac (A⊕B)→ₗ[ℂ]Dirac B) ?_) x; intro u v; simp only [LinearMap.comp_apply,vary_mul,near_d,ignores_far,mul_zero,add_zero,margins,integration]; simp -- use exact args?
lemma lateral (i:Pairs B)(x:Dirac (A⊕B)): marginal A B (vary (besideK A i) x)= vary i (marginal A B x):=by
    refine LinearMap.congr_fun (passthrough (A:=A) (B:=B) ((marginal A B).comp (vary (besideK A i))) ((vary i).comp (marginal A B)) ?_) x; intro u v; simp only [LinearMap.comp_apply,vary_mul,far_d,ignores_near,zero_mul,zero_add]; rw [show grade (near A B u)=near A B (grade u) from pass_grade ..,margins,margins,map_smul,Massive.Transfer.berezin_grade] -- replace
lemma lateral_lap (T:Sour B)(x:Dirac (A⊕B)): marginal A B (lap (jointChoice 0 T) x)= lap T (marginal A B x):=by
    rw [lap_apply,lap_apply]; simp [jointChoice,Fintype.sum_sum_type]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; change T i j • marginal A B (vary (besideK A (.inl i)) (vary (besideK A (.inr j)) x))= _; rw [lateral (.inl i), lateral (.inr j)]
end YM.QCD.Grass.Ward
#print axioms YM.QCD.Grass.Ward.marginal_mark
#print axioms YM.QCD.Grass.Ward.lateral_lap
