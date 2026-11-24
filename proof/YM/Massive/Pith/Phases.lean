import YM.QCD.Dust.June
/-!
### Diagonal vector torus invariance
Fiber-carrying perturbations here. Four condition, opposite imbalance, off-flavor pairs, and analogues of `Stew.known` will let us still project onto color- and spin-scalar on-site bill *per flavor* at price bounded by the old `preMoment`. Uses Pant.Court, Stew.Life for adapted lemmas.
-/
set_option autoImplicit false
set_option linter.unusedSimpArgs false -- matching parallel cases in both L2 and Frobenius contexts
noncomputable section
namespace YM.QCD.Pith
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open Revolve Stew Reggae Brick
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ} {v:Strut c}{k:Spike}{g:Site c→ℂ}
def Phases (x:EvenA c N) : Prop := ∀ w: Flavor N→ℂ, Matrix.diagonal w∈unitary _ → sways (flute (Lat.Row c) (Matrix.diagonal w)) x=x
lemma fitP (x:EvenA c N)(h:Fit x): Phases x:=fun _ hw => h _ hw
lemma phase_ite0 : Phases (0:EvenA c N):= fun _ _=>map_zero _
lemma phase_id : Phases (1: EvenA c N):=fun _ _=>map_one _
lemma phase_add {x y:EvenA c N}(h:Phases x)(hp:Phases y):Phases (x+y) :=fun p q=> (map_add _ _ _).trans (congr_arg₂ _ (h p q) (hp p q))
lemma phase_mul {x y:EvenA c N}(h:Phases x)(hp:Phases y):Phases (x*y) :=fun p q=> (map_mul _ _ _).trans (congr_arg₂ _ (h p q) (hp p q))
lemma phase_sub {x y:EvenA c N}(h:Phases x)(hp:Phases y):Phases (x-y) :=fun p q=> (map_sub _ _ _).trans (congr_arg₂ _ (h p q) (hp p q))
lemma complexFactor {D:Type*}[DecidableEq D][Fintype D] (x:ℂ)(y:Matrix D D ℂ)(z:Patio (Pairs D)): sways y (x • z)=x • sways y z:=Subtype.ext (map_smul (disguise y) x z.val)
lemma phase_r (s:ℝ)(x:EvenA c N)(h:Phases x):Phases (s • x):=fun _ q=> (Loom.Fleet.eSM _ (OrbitG.phare _) ..).trans (congr_arg (s • ·) (h _ q))
lemma phase_c (s:ℂ)(x:EvenA c N)(h:Phases x):Phases (s • x):=fun _ q=> (complexFactor s _ x).trans (congr_arg (s • ·) (h _ q))
lemma full (D:Type*)[DecidableEq D](w:Flavor N→ℂ): flute D (Matrix.diagonal w)=Matrix.diagonal (fun x:D×Flavor N=> w x.2):=by
   ext ⟨i,h⟩ ⟨j,g⟩; by_cases h':i=j <;> by_cases hp:h=g <;> simp [flute,Matrix.one_apply,Matrix.diagonal_apply,h',hp]
lemma flatV (T:Type*)[DecidableEq T](z:ℂ): Matrix.diagonal (fun _:T=> z)= z • (1 : Matrix T T ℂ):=by
    ext i j; by_cases h:i=j<;> simp [Matrix.diagonal_apply,Matrix.one_apply,Matrix.smul_apply,h]
lemma scalar (x:ℂ) (hx:star x*x=1) (v:EvenA c N)(h:Phases v): sways (x • (1:Matrix (Modes c N) (Modes c N) ℂ)) v=v:= by
    have he:= h (fun _=>x) ((flatV (Flavor N) x).symm ▸ (unitaryV x _ hx)); rw [full,flatV (Lat.Row c × Flavor N)] at he; exact he
lemma phase_wire (X:Sheet c)(v:EvenA c N)(h:Phases v):Phases (sways (copies N X) v):=by intro g hh; rw [← choirT,h _ hh]
lemma phase_conj (v:EvenA c N)(h:Phases v):Phases ((OrbitG.spark _).passL v):=by intro g hh; rw [←novel,h _ hh]
lemma facadeP (v: EvenA c N)(h: Phases v)(x:ℂ)(X:Sheet c)(hx:star x*x=1): sways (copies N (x • X)) v= sways (copies N X) v:=by
    rw [copies_skim,← one_mul (copies _ X),← Matrix.smul_mul,← leaps,scalar x hx _ h, one_mul] -- one_mul RHS also expanded? nth_rw
lemma coinP (v:EvenA c N)(h:Phases v){p:Strut c}{d d':Site c→ℂ}{Z P:Spike}(he: Warrant p d Z)(hv:Warrant p d' P): Diode N p Z d v=Diode N p P d' v:=by
    obtain ⟨s,hS,H⟩:= Strut.faith he hv
    apply Eq.trans _ (facadeP v h s (haze p P d') hS)
    apply congr_arg (fun X=> sways (copies N X) v)
    change rides _ _=s • rides _ _; rw [ride_smul]; exact congr_arg _ (funext H)
lemma gammaP (v:EvenA c N)(h:Phases v){p:Strut c}{d:Site c→ℂ}{Z:Spike}(hp:Warrant p d Z): Regal c N (Diode N p Z d v)=Diode N p Z d (Regal c N v):=by
    let Vw:= (OrbitG.spark _).passL v
    obtain ⟨x,hx,hC⟩:= upright hp
    have hh : haze p Z d*chirality c=x • (chirality c*haze p Z d):=by
       change rides (act p) (lightP p Z d) *rides (Equiv.refl (Site c)) (fun _=>J0)=x • (rides (Equiv.refl (Site c)) (fun _=>J0)* rides (act p) (lightP p Z d)); rw [ride_mul,ride_mul,ride_smul,Equiv.trans_refl,Equiv.refl_trans]; exact congr_arg _ (funext hC)
    change sways (copies N (chirality c)) ((OrbitG.spark _).passL (_))=sways _ (sways (copies N (chirality c)) Vw); unfold Diode; rw [novel,leaps,leaps,← copies_mul,← copies_mul,hh]; exact facadeP Vw (phase_conj v h) x _ hx
local notation "J"=> Modes c N
lemma clean (x: EvenA c N)(h:Phases x): panel 2 x.val=form (grasp x.val):= kent x.val (unbalanced _ (congr_arg Subtype.val (scalar Complex.I (by simp) x h)))
lemma adapted (L:Matrix J J ℂ)(x:EvenA c N)(h: Phases x): grasp (disguise L x.val)= star L * grasp x.val * L:=by rw [←breast, sport,clean x h, disguise, form_map,Matrix.transpose_transpose,gravid,Matrix.mul_assoc]
lemma mirrorP (L:Matrix J J ℂ)(x:EvenA c N)(h: Phases x): grasp (disguise L (surf _ x.val))= star L*star (grasp x.val)*L:=by rw [←breast,sport,toned, clean x h,Port.surf_form,disguise, form_map, Matrix.transpose_transpose,gravid,Matrix.mul_assoc]
lemma offQ (x: EvenA c N) (h:Phases x)(i j:Row c)(k l:Flavor N)(hp:k≠l): grasp x.val (i,k) (j,l)=0:=by
    let p:=grasp x.val
    let R:Flavor N→ℂ:= fun i=> if k=i then -1 else 1; let L:= Matrix.diagonal R
    have hh:L∈unitary _:=by
       have hL : star L=L:=by
          ext a b; rcases eq_or_ne a b with hv|hv
          · subst b; simp only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,L,Matrix.diagonal_apply,if_true]; exact lines k a
          simp [hv,Ne.symm hv,L, Matrix.diagonal_apply, R,Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
       have hp:L*L=1:=by ext a b; by_cases he:a=b <;> by_cases hh:k=b <;> simp [L, R,Matrix.diagonal_apply, Matrix.diagonal_mul_diagonal,Matrix.one_apply,he,hh]
       constructor <;> rw [hL,hp]
    let M:=flute (Lat.Row c) L; have hu:M*p=p*M:=by
       have hz:p=star M*p*M:= (Eq.trans (congr_arg grasp (congr_arg Subtype.val (h R hh)).symm) (Pith.adapted M x h)); nth_rw 1 [hz]; rw [← Matrix.mul_assoc,← Matrix.mul_assoc,(unit_f hh).2, one_mul]
    have hx : -p (i,k) (j,l)=p (i,k) (j,l):=by
       have hz := congr_fun (congr_fun hu (i,k)) (j,l); unfold M L at hz; rw [Pith.full, Matrix.diagonal_mul,Matrix.mul_diagonal] at hz; simpa [R,hp] using hz
    change p (i,k) (j,l)=0
    apply Complex.ext; · have hp:=congr_arg Complex.re hx; rw [Complex.neg_re] at hp; rw [Complex.zero_re]; linarith
    have hp:=congr_arg Complex.im hx; rw [Complex.neg_im] at hp; rw [Complex.zero_im]; linarith
lemma fibers (x: EvenA c N) (h:Phases x) : grasp x.val= Matrix.blockDiagonal fun b:Flavor N=> feeF b x:=by
    ext ⟨i,k⟩ ⟨j,l⟩; by_cases hp:k=l
    · subst l; simp [Matrix.blockDiagonal_apply,feeF]
    rw [offQ x h i j k l hp]; simp [hp,Matrix.blockDiagonal_apply]
lemma riteP (v:EvenA c N)(b : Flavor N)(X: Sheet c)(h:Phases v): feeF b (sways (copies N X) v)=star X * feeF b v*X:=by
   let T:=copies N X; have he : grasp (sways T v).val=star T*grasp v.val*T:=Pith.adapted T v h
   rw [fibers v h] at he; unfold T at he; rw [← copies_star] at he; unfold copies at he; rw [← Matrix.blockDiagonal_mul,← Matrix.blockDiagonal_mul] at he
   ext i j; unfold feeF; simp only [Matrix.of_apply]; exact (congr_fun (congr_fun he (i,b)) (j,b)).trans (by rw [Matrix.blockDiagonal_apply,if_pos (by rfl)];rfl)
lemma burstP (v:EvenA c N)(b: Flavor N)(h:Phases v): feeF b (Regal c N v)=star (chirality c)*star (feeF b v)*chirality c:=by
   let X:=chirality c; have he:=mirrorP (copies N X) v h; rw [fibers v h,← copies_star] at he
   have hp : star (Matrix.blockDiagonal (fun b: Flavor N=>feeF b v))=Matrix.blockDiagonal (fun b: Flavor N=> star (feeF b v)):=by
      ext ⟨i,j⟩ ⟨k,l⟩; by_cases hf:l=j<;> simp [Matrix.blockDiagonal_apply,Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,hf,Ne.symm]
   rw [hp] at he; unfold copies at he; rw [← Matrix.blockDiagonal_mul,← Matrix.blockDiagonal_mul] at he
   ext i j; exact (congr_fun (congr_fun he (i,b)) (j,b)).trans (by rw [Matrix.blockDiagonal_apply,if_pos (by rfl)])
end YM.QCD.Pith
#print axioms YM.QCD.Pith.fibers
