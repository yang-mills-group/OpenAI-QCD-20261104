import YM.Massive.PCAC.Bead
/-!
# Vector mass presentation. All real Wilson regulators (the very ones in Scheme.run).
Order of `probe` signs matches psi bar (minus common bar psi notation).
Read all discrete divergences in bare spacing units.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC
open QCD QCD.Grass QCD.Lat Lattice Wilson RG Function Filter MeasureTheory QCD.Grass.Ward
open YM.Next.Free
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator Classical ComplexOrder
variable {A B:Type*} [Fintype A][Fintype B]
variable {c f:Side}{n N j k F:ℕ}
variable (P:Flight j k)(K:KernelChoices)(h:f.val=c.val*P.L.val) (β w:ℝ)(hk:P.patch.Branches K su)
open Tide NormedSpace
open Finset
variable (R:Regulator c F)(a b:Flavor F)(u v:Site c) (U:Grid c)
local notation "B!"=> Flavor F
local notation "Y"=> flavorW 1 a b c
local notation "y"=> localF u 1 a b
abbrev leanD (U:Grid c):= copies F (bareD R.t U 0)
local notation "K"=>leanD R -- K override above; macro shadow
-- algebra of offset. `dX` all Wilson free relative comparisons.
local notation "Q"=> Onsite.offset R.m (Finset.univ:Support c)
lemma bare0 : R.D U=K U+Q:=Onsite.unmasked R U
lemma amid : Commute (K U) Y:=by unfold flavorW; rw [on_spin_one]; unfold Commute SemiconjBy; exact (Sway.column (bareD R.t U 0) (spot a b)).symm
lemma sails(a b:Flavor F)(X:Spike): Q*flavorW X a b c=(R.m a:ℂ) • flavorW X a b c :=by
    unfold Onsite.offset; ext ⟨i,w⟩ ⟨j,z⟩; rw [Matrix.diagonal_mul]; unfold flavorW spot; by_cases hw:w=a; · subst w; simp
    simp [hw]
lemma ridesF(a b:Flavor F)(X:Spike) : flavorW X a b c*Q=(R.m b:ℂ) • flavorW X a b c:=by
    unfold Onsite.offset; ext ⟨i,w⟩ ⟨j,z⟩; rw [Matrix.mul_diagonal]; unfold flavorW spot; by_cases hz:z=b; · subst z; simp [mul_comm (onSpin c X i j)] -- style
    simp [hz]
lemma around : Commute Q (zone F u):=by unfold zone Onsite.offset Commute SemiconjBy; rw [Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]; apply congr_arg; ext1 i; exact mul_comm .. 
lemma lay_left(X:Spike) : R.D U* localF u X a b= (R.m a:ℂ) • localF u X a b+ K U * localF u X a b:=by rw [bare0,add_mul]; unfold localF; rw [←mul_assoc Q, (around R u).eq,mul_assoc (zone F u) Q,sails, Matrix.mul_smul]; exact add_comm ..
lemma lay_right(X:Spike) : localF u X a b * R.D U= (R.m b:ℂ) • localF u X a b + localF u X a b * K U:=by rw [bare0,mul_add]; unfold localF; rw [mul_assoc (zone F u) _ Q,ridesF, Matrix.mul_smul]; exact add_comm ..
-- orienting divergence toward u (inflow)
local notation "Λ"=> zone F
noncomputable def jets (V:Grid c): Sour (Modes c F):= (Λ v * K V * Λ u- Λ u * K V * Λ v)* Y
lemma stream : jets R a b u v U= -jets R a b v u U:=by unfold jets; rw [← neg_mul, neg_sub]
lemma diverge : ∑ v,jets R a b u v U= K U*y-y*K U:=by
    have ht(u): (Λ u)*Y=Y*Λ u:= (commute_here a b u 1).eq; unfold jets localF; rw [←sum_mul,sum_sub_distrib, ←sum_mul, ←sum_mul, ←mul_sum,cells,one_mul,mul_one]; rw [sub_mul,mul_assoc,mul_assoc (Λ u), (amid R a b U).eq, mul_assoc] -- ht no? D*zone*Y, zone*D*Y

abbrev Contacts (u v:Site c):Prop:=∃ a:Axis,v=u+step a ∨ v=u-step a
lemma symmetric (h:Contacts u v): Contacts v u:=by
    obtain ⟨a,ha|ha⟩:=h; · subst v; exact ⟨a,Or.inr (by simp)⟩
    subst v; exact ⟨a,Or.inl (by simp)⟩
lemma kinetic (i j:Row c)(h:i.1≠j.1)(hx:¬ Contacts i.1 j.1): bareD R.t U 0 i j=0:=by
     have hh:i≠j:=fun hh=> h (congr_arg Prod.fst hh)
     have ht(a:Axis): singleHop R.t U a i j=0:=by rw [hop_read, if_neg (fun he=> hx ⟨a,Or.inl he.symm⟩),if_neg (fun he=>hx ⟨a,Or.inr he.symm⟩),add_zero]
     simp only [bareD,Matrix.add_apply,Matrix.smul_apply,Matrix.sum_apply,Matrix.sub_apply,ht,Matrix.one_apply,if_neg hh]; simp
lemma separates (h:u≠v)(hs:¬ Contacts u v): Λ u * K U * Λ v =0:=by
    ext i j; rw [zright,zleft]; simp only [Matrix.zero_apply]; split
    swap; rfl
    next h1=> split
              next h2=>
                 unfold leanD copies; rw [Matrix.blockDiagonal_apply]; split; exact kinetic R U i.1 j.1 (by rwa [h2,h1]) (by rwa [h2,h1]); rfl
              next _=> rfl
lemma currents_active (hv:¬ Contacts u v): jets R a b u v U=0:=by
    by_cases h:u=v; · subst v; unfold jets; rw [sub_self,zero_mul]
    unfold jets; rw [separates R v u U (Ne.symm h) (fun hh=> hv (symmetric v u hh)),separates R u v U h hv,sub_self,zero_mul]

lemma form_smul (u:ℂ)(X:Sour A) : form (u • X)=u • form X:=by simp [form,smul_sum,mul_smul]
lemma form_sub (X W:Sour A): form (X-W)=form X-form W:=by apply eq_sub_of_add_eq; rw [← form_add, sub_add_cancel]
def couples (A:Type*)[Fintype A] : Sour A →ₗ[ℂ]Dirac A:= { toFun:=form,map_add':=form_add,map_smul':=form_smul }

noncomputable def scalarProbe (X:Spike):Insertion c F:= ContinuousMap.const _ (form (localF u X a b))
lemma leanD_cont : Continuous (leanD R):= by
   change Continuous (fun V:Grid c=> Kit.choir F (bareD R.t V 0)); apply (Kit.choir_cont F).comp (f:=fun V:Grid c=> bareD R.t V 0); fun_prop
noncomputable def current : Insertion c F := ⟨fun U=> form (jets R a b u v U), by
     have hp : Continuous (jets R a b u v):= by unfold jets; have hh:=leanD_cont R; fun_prop
     exact (couples _).continuous_of_finiteDimensional.comp hp ⟩
lemma swapped : current R a b u v= -current R a b v u:=by ext1 i; change form _ = - _; rw [stream]; exact map_neg (couples _) _
lemma here (hv:¬ Contacts u v): current R a b u v=0:=ContinuousMap.ext fun U=> (congr_arg form (currents_active R a b u v U hv)).trans (map_zero (couples _))
lemma probe_bare (p:Bool)(T:Sour (Modes c F)): applyMark p T (R.density U)= R.density U*form (if p then T*R.D U else R.D U*T):=by rw [Regulator.density_apply, map_smul, mark_gauss,smul_mul_assoc]
-- relation at point equality of entire functions. No spectators yet.
local notation "δ"=> ((R.m a:ℂ)-(R.m b:ℂ))
theorem vectorWard : mark false y R.density - mark true y R.density = R.density*(δ • scalarProbe a b u 1+∑ v:Site c,current R a b u v):=by
     ext1 i; rw [ContinuousMap.sub_apply,ContinuousMap.mul_apply,ContinuousMap.add_apply,ContinuousMap.sum_apply,ContinuousMap.smul_apply]; change applyMark _ y _-applyMark _ y _=_; simp_rw [probe_bare]; rw [← mul_sub]; simp only [Bool.false_eq_true,↓reduceIte]; apply congr_arg; rw [← form_sub]; change _= _ + ∑ v:Site c,couples _ (jets R a b u v i)
     rw [← map_sum, diverge]; rw [show R.D i*y-y*R.D i = δ • y+ (K i*y-y*K i) by rw [lay_left,lay_right,sub_smul]; abel,form_add, form_smul]; rfl
-- axial sum, no misleading Wilson cancellation. spin violation remains.
noncomputable def axial_rest(X:Spike): Insertion c F:= ⟨fun i=> form (K i*localF u X a b+localF u X a b*K i),by apply (couples _).continuous_of_finiteDimensional.comp (f:=fun i=> K i*localF u X a b+localF u X a b*K i); have hh:=leanD_cont R; fun_prop⟩
theorem axialWard (X:Spike) : let p:=localF u X a b; mark false p R.density+mark true p R.density= R.density*((((R.m a:ℂ)+(R.m b:ℂ)):ℂ) • scalarProbe a b u X+ axial_rest R a b u X):=by
     intro p; ext1 i; unfold mark; simp only [ContinuousMap.add_apply,ContinuousMap.mul_apply,ContinuousMap.smul_apply,stroll_at,probe_bare,Bool.false_eq_true,↓reduceIte]; rw [←mul_add]; apply congr_arg; rw [← form_add]; rw [show R.D i*p+p*R.D i=((R.m a:ℂ)+(R.m b:ℂ)) • p+(K i*p+p*K i) from ?_,form_add, form_smul]; rfl
     unfold p; rw [lay_left,lay_right,add_smul]; abel
end YM.Massive.PCAC
#print axioms YM.Massive.PCAC.vectorWard
