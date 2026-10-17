use std::process::Command;

#[test]
fn compiled_runtime_operations_preserve_language_behavior() {
    let script = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("scripts")
        .join("runtime_intrinsics.napalm");
    let output = Command::new(env!("CARGO_BIN_EXE_Napalm"))
        .arg(script)
        .output()
        .expect("execute runtime intrinsic regression script");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&output.stdout).replace("\r\n", "\n"),
        concat!(
            "[0, null, null]\n",
            "[1, 2, 3]\n",
            "[1, 3, null, null]\n",
            "[1, 20, 3, null, null, 60]\n",
            "[1, 20, null, null, null]\n",
            "[6, 9, null, 4]\n",
            "[1, 20, null, null]\n",
            "[42, 42, 42]\n42\n",
            "[7, 7, 7, 7]\n[42, 42]\n",
            "[2, 3, 4]\n[3, 4]\n6\n",
            "[6, true, true]\n[true, true, false]\n",
            "[1, 3, -1]\n[3, 1, 6]\n",
            "[\"apa\", \"alm\", \"\"]\n",
            "[\"apa\", \"nap\", \"alm\"]\n",
            "[\"Napalm\", \"Napalm \", \" Napalm\"]\n",
            "[\"NAPALM!\", \"napalm!\"]\n",
            "[\"STRASSE\", \"\u{e9}\"]\n",
            "[5, \"\u{e9}\", \"caf\", 3]\n",
            "[7, false, 0]\nnull\n",
        ),
    );
}
