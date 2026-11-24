import YM.QCD.Eyrie.Post

/-! # Unlimited after-L uniform priced maps. Still literal shape and asks.

Output scalar constant can be selected after q; this predicates across a
gathering of all inputs for actual proof using Budgets. L poor adequate for
first- and second-born kernels. Inheritance needs direct scaling proofs separate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Eyrie
open Function Filter Lattice Wilson Lat Kit Cost Finset Run Revolve Metric Push.Uniform
open Quarry Tree RG Precision
open scoped Topology Matrix Matrix.Norms.L2Operator BigOperators Classical ContDiff
variable {T : Type*}
structure Works (S : Type*) where
  n : S→ Side
  s : S→ Side
  ratio (u:S) : Ratio (s u) (n u)
namespace Works
variable (P : Works T)
-- station directions used always at coarse sites. Elements are maps from its coords.
def period (y:T)(F:Bool):Side:=if F then P.n y else P.s y
-- give sigma by pattern instead of by_cases
abbrev Names (y:T)(F:Bool):= Row (P.period y F)
def origin (y:T)(F:Bool): P.Names y F→ Site (P.n y):= match F with
  | true=> fun i=>i.1
  | false=> fun i=> (P.ratio y).embed i.1
lemma counted (y:T)(F:Bool): Multiplicity (P.origin y F) (Fintype.card Fiber):=by
  cases F
  · exact multIJ _
  exact multIF _
abbrev Board (A B:Bool) := ∀ u:T, Cnr (P.s u) → Matrix (P.Names u A) (P.Names u B) ℂ
def League {A B:Bool} (F:P.Board A B):Prop:= ∃ a C:ℝ,0 < a ∧ 0≤C ∧ ∀ y,glyph (beam (P.ratio y)) Push.Uniform.bolt (P.origin y A) (P.origin y B) (F y) a C
namespace League
variable {P} {A B C F : Bool} {L K:P.Board A B}
lemma identity (P : Works T)(A) : P.League (A:=A) (B:=A) (fun _ _=>1):= ⟨1,1,zero_lt_one,zero_le_one,fun _=> glyph.uni zero_lt_one⟩
lemma zeros (P : Works T)(A B: Bool):P.League (A:=A) (B:=B) (fun _ _=>0):=⟨1,0,zero_lt_one,le_refl 0,fun _ _ _=> (Flock.hush _ zero_lt_one).patron (by simp)⟩
lemma plus (h:P.League L)(p:P.League K):P.League (A:=A) (B:=B) (fun y x=>L y x+ K y x):=by
  obtain ⟨a,b,hb,hu,H⟩:=h; obtain ⟨c,d,hc,h',D⟩:=p; have he:=lt_min hb hc; exact ⟨min a c,b+d,he,add_nonneg hu h',fun i=> ((H i).reduces he (min_le_left ..) hu le_rfl).plus ((D i).reduces he (min_le_right ..) h' le_rfl)⟩
lemma minus (h:P.League L):P.League (A:=A) (B:=B) (fun y x=> - L y x):=by obtain ⟨a,b,hb,hu,H⟩:=h; exact ⟨a,b,hb,hu,fun i=> (H i).minus⟩
lemma down (h:P.League L)(p:P.League K):P.League (A:=A) (B:=B) (fun y x=>L y x-K y x):=by simp_rw [sub_eq_add_neg]; exact h.plus p.minus
lemma connects {D:P.Board B C}(h:P.League L)(p:P.League D):P.League (A:=A) (B:=C) (fun y x=>L y x* D y x):=by
  obtain ⟨a,b,hb,hu,H⟩:=h; obtain ⟨c,d,hc,h',Q⟩:=p; have he:=lt_min (show 0<a/4 by positivity) hc; let z := min (a/4) c
  refine ⟨z,4*b*d*((Fintype.card Fiber:ℝ)*countCost z),he,by have hh:=count_pos he; unfold z; positivity,fun i=> ?_⟩
  exact (H i).comp ((Q i).reduces he (min_le_right ..) h' le_rfl) he (by linarith [min_le_left (a/4) c]) (P.counted i B) hu h'
lemma up (h:P.League L):P.League (A:=B) (B:=A) (fun y x=> (L y x)ᴴ):=by
  obtain ⟨a,b,hb,hu,H⟩:=h; have hx : 0<a/3:=by positivity
  exact ⟨_,_,hx,hu,fun i=> (H i).flip hx (by linarith)⟩
lemma invert (L:P.Board A A)(h:P.League L)(hp : ∀ y, IsUnit (L y 0).det)(hd: P.League (A:=A) (B:=A) fun y _=>(L y 0)⁻¹): P.League (A:=A) (B:=A) (fun y x=> (L y x)⁻¹) := by
  obtain ⟨a,b,hb,hu,H⟩:=h; obtain ⟨c,d,hc,h',Q⟩:=hd; have he:=lt_min hb hc; let v := min a c; let u:=v/64; have hv : 0<u:= div_pos he (by norm_num)
  have ht i:= Eyrie.entries (L i) ((H i).reduces he (min_le_left ..) hu le_rfl) (P.counted i A) hv (by unfold u v; linarith) hu h' (hp i) (fun a z=> (((Q i).reduces he (min_le_right ..) h' le_rfl) a z).born)
  refine ⟨_,_,hv,?_,ht⟩
  have ht:=count_pos hv; have hh:= count_pos (show 0<4*u by positivity); have hw:=count_pos (show 0<4*(4*u) by positivity); positivity
lemma knows {G:P.Board A B}(h:P.League L)(he:∀ y, G y =ᶠ[𝓝 0] L y): P.League G:=by
  obtain ⟨u,v,hu,hv,H⟩:=h; exact ⟨_,_,hu,hv,fun y i j=> (H y i j).aliasG ((he y).mono fun _ hk=> congr_arg (fun z=> z i j) hk)⟩
end League
end Works
end YM.QCD.Eyrie
