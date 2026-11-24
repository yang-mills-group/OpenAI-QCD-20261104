import YM.QCD.Brick.Glove
/-! # Cover transports to both particle/antiparticle gradients. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Brick
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Garden Fork Leaf Tee Flume YM.Next.Free Laurent
variable {c f:Side} {j k N m:ℕ}(B:Plan j)(F:Flight j k) (h:f.val=c.val*F.L.val){p r q t :ℝ}
set_option quotPrecheck false
abbrev Crate (c:Side)(N:ℕ):= Alg (Keys c N)
abbrev tube (N:ℕ) (X:Kit.Rail f c) (p:Keys f N): Crate c N:= changeVars (powerF (N:=N) X) (atom p)
abbrev stemF (F:ℕ):ℝ:=2*Jets.Sun.fingers F
lemma crystals (U: Site c →ℝ): (∑ i:Keys c N,U (locationP i))= stemF N * ∑ j,U j:=by
   unfold stemF; change ∑ i: Modes c N ⊕ Modes c N,U (locationP i)=_; simp_rw [Fintype.sum_sum_type]; unfold Modes; simp_rw [Fintype.sum_prod_type,locationP, Sum.elim_inl, Sum.elim_inr]; unfold Jets.Sun.fingers; simp only [sum_const,nsmul_eq_mul, card_univ,Flavor,Fintype.card_fin, ← mul_assoc, ← Finset.mul_sum]; rw [show Fintype.card (Lat.Fiber)=12 by simp [Lat.Fiber,Hue,Pinor]]; ring -- fix
lemma radiate (Y:Kit.Rail f c)(x:Keys f N)(S:Ratio c f)(A:ℝ)(hv:∑ j,meets S (locationP x) 2 j * ‖cell Y (locationP x) j‖ ≤ A) (ht:0≤t): Stew.plank (S.parent (locationP x)) t (tube N Y x) ≤ stemF N * A *t:=by
   let Q:= S.parent (locationP x); let u (j:Site c):= meets S (locationP x) 2 j; let L:= locationP x
   have hp(i): Stew.plank Q t (atom (i:Keys c N))= u (locationP i)*t:=by rw [Stew.plank,reachA i ht]; unfold Stew.lens u meets Q; rw [separation_comm]
   rw [tube,change_atom]; apply (vc_sum ..).trans; simp_rw [vc_scale]; apply le_trans (sum_le_sum (g:=fun i=> u (locationP (i:Keys c N)) * ‖cell Y L (locationP i)‖ *t) (fun i _=> ?_)) ?_; swap
   · change _*Stew.plank _ _ _≤ _; rw [hp]; exact (mul_le_mul_of_nonneg_right (duty ..) (mul_nonneg (meets_nn ..) ht)).trans_eq (by ring)
   rw [← sum_mul,crystals (fun i: Site c=> u i * ‖cell Y L i‖)]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv (by unfold stemF Jets.Sun.fingers; positivity)) ht
abbrev Accent (N:ℕ):= Pairs (Fiber × Flavor N)
def placeQ (x:Site f) (i:Fiber×Flavor N): Modes f N:= ((x,i.1),i.2)
def pitchQ (x:Site f)(i:Accent N): Keys f N:=Sum.map (placeQ x) (placeQ x) i
lemma residents (x:Site f)(y:Accent N): locationP (pitchQ x y)=x:=by rcases y with a|a<;> rfl
lemma karma (Z:Kit.Rail f c)(x j) (p:Axis): cell (Flume.after Z p) x j=(seam 0 x p) • cell Z (x+step p) j-cell Z x j:=by ext i w; exact Flume.afterwards ..
lemma curtains (Z: Kit.Rail f c)(x j)(p:Axis): cell (railDay (Flume.after Z p)) j x=(seam 0 x p) •cell (railDay Z) j (x+step p)-cell (railDay Z) j x:=by
   simp_rw [railDay,Garden.halo,cell_flip]; rw [karma,star_sub,star_smul]; obtain hx|hx:= seam_cases 0 x p<;> rw [hx] <;>simp [Matrix.mul_sub,Matrix.sub_mul]
lemma freezeW (Z: Kit.Rail f c)(x:Site f)(y: Accent N)(p:Axis)(i:Keys c N) : powerF (Flume.after Z p) (pitchQ x y) i= seam 0 x p * powerF Z (pitchQ (x+step p) y) i - powerF Z (pitchQ x y) i :=by
    rcases y with k|k<;>rcases i with ⟨⟨z,l⟩,b⟩|⟨⟨z,l⟩,b⟩
    · change (if k.2=b then cell (Flume.after Z p) x z k.1 l else 0)=_*(if k.2=b then _ else 0)-(if k.2=b then _ else 0)
      split; exact Matrix.ext_iff.mpr (karma Z x z p) k.1 l
      simp
    · change (0:ℂ)=_*0-0; simp
    · change (0:ℂ)=_*0-0; simp
    change (if b=k.2 then cell (railDay (Flume.after Z p)) z x l k.1 else 0)= _*(if b=k.2 then _ else 0)-(if b=k.2 then _ else 0)
    split; exact Matrix.ext_iff.mpr (curtains Z x z p) l k.1
    simp
lemma turns (Z: Kit.Rail f c)(p:Axis)(x:Site f)(i:Accent N): tube N (Flume.after Z p) (pitchQ x i)= (seam 0 x p) • tube N Z (pitchQ (x+step p) i)-tube N Z (pitchQ x i):=by
    unfold tube; simp_rw [change_atom,freezeW,sub_smul,sum_sub_distrib,Finset.smul_sum, mul_smul]
-- alias-wrapped normalized fields
variable (o: Site f)
def loomQ (X:Kit.Rail f c)(v:Cover)(i:Accent N): Crate c N:= occ o v • tube N X (pitchQ (o+wrap f v) i)
lemma lilt (x:Cover) (p:Axis) (i:Accent N)(X : Kit.Rail f c): loomQ o (Flume.after X p) x i = loomQ o X (x+ step p) i- loomQ o X x i:=by
    unfold loomQ; rw [sign_rate,map_add, ← add_assoc]; rw [show wrap f (step p)=step p from ?_]; rotate_left; · simp -- lemma
    rw [turns, smul_sub,smul_smul]; congr 2
    have h: occ (o+wrap f x) (step p)=seam 0 (o+wrap f x) p := by
       rw [show (step p:Cover) = stop 0 [posDir p] from (by change step p= 0 +step p; rw [zero_add]), ← Quarry.occ_rays]
       unfold Revolve.shimmer Revolve.glint; simp [Step.used, posDir, Revolve.shimmer] -- namespaces
    rw [h]
end YM.QCD.Brick
