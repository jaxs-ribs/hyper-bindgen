use anyhow::{Context, Result};
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use syn::{self, Attribute, ImplItem, Item, Type};
use walkdir::WalkDir;
use toml::Value;

// Helper functions for naming conventions
fn to_kebab_case(s: &str) -> String {
    // First, handle the case where the input has underscores
    if s.contains('_') {
        return s.replace('_', "-");
    }
    
    let mut result = String::with_capacity(s.len() + 5); // Extra capacity for hyphens
    let chars: Vec<char> = s.chars().collect();
    
    for (i, &c) in chars.iter().enumerate() {
        if c.is_uppercase() {
            // Add hyphen if:
            // 1. Not the first character
            // 2. Previous character is lowercase
            // 3. Or next character is lowercase (to handle acronyms like HTML)
            if i > 0 && 
               (chars[i-1].is_lowercase() ||
                (i < chars.len() - 1 && chars[i+1].is_lowercase()))
            {
                result.push('-');
            }
            result.push(c.to_lowercase().next().unwrap());
        } else {
            result.push(c);
        }
    }
    
    result
}

// Validates a name doesn't contain numbers or "stream"
fn validate_name(name: &str, kind: &str) -> Result<()> {
    // Check for numbers
    if name.chars().any(|c| c.is_digit(10)) {
        anyhow::bail!("Error: {} name '{}' contains numbers, which is not allowed", kind, name);
    }
    
    // Check for "stream"
    if name.to_lowercase().contains("stream") {
        anyhow::bail!("Error: {} name '{}' contains 'stream', which is not allowed", kind, name);
    }
    
    Ok(())
}

// Remove "State" suffix from a name
fn remove_state_suffix(name: &str) -> String {
    if name.ends_with("State") {
        let len = name.len();
        return name[0..len-5].to_string();
    }
    name.to_string()
}

// Extract wit_world from the #[hyperprocess] attribute using the format in the debug representation
fn extract_wit_world(attrs: &[Attribute]) -> Result<String> {
    for attr in attrs {
        if attr.path().is_ident("hyperprocess") {
            // Convert attribute to string representation
            let attr_str = format!("{:?}", attr);
            println!("Attribute string: {}", attr_str);
            
            // Look for wit_world in the attribute string
            if let Some(pos) = attr_str.find("wit_world") {
                println!("Found wit_world at position {}", pos);
                
                // Find the literal value after wit_world by looking for lit: "value"
                let lit_pattern = "lit: \"";
                if let Some(lit_pos) = attr_str[pos..].find(lit_pattern) {
                    let start_pos = pos + lit_pos + lit_pattern.len();
                    
                    // Find the closing quote of the literal
                    if let Some(quote_pos) = attr_str[start_pos..].find('\"') {
                        let world_name = &attr_str[start_pos..(start_pos + quote_pos)];
                        println!("Extracted wit_world: {}", world_name);
                        return Ok(world_name.to_string());
                    }
                }
            }
        }
    }
    anyhow::bail!("wit_world not found in hyperprocess attribute")
}

// Convert Rust type to WIT type, including downstream types
fn rust_type_to_wit(ty: &Type, used_types: &mut HashSet<String>) -> Result<String> {
    match ty {
        Type::Path(type_path) => {
            if type_path.path.segments.is_empty() {
                return Ok("unknown".to_string());
            }
            
            let ident = &type_path.path.segments.last().unwrap().ident;
            let type_name = ident.to_string();
            
            match type_name.as_str() {
                "i32" => Ok("s32".to_string()),
                "u32" => Ok("u32".to_string()),
                "i64" => Ok("s64".to_string()),
                "u64" => Ok("u64".to_string()),
                "f32" => Ok("f32".to_string()),
                "f64" => Ok("f64".to_string()),
                "String" => Ok("string".to_string()),
                "bool" => Ok("bool".to_string()),
                "Vec" => {
                    if let syn::PathArguments::AngleBracketed(args) = 
                        &type_path.path.segments.last().unwrap().arguments
                    {
                        if let Some(syn::GenericArgument::Type(inner_ty)) = args.args.first() {
                            let inner_type = rust_type_to_wit(inner_ty, used_types)?;
                            Ok(format!("list<{}>", inner_type))
                        } else {
                            Ok("list<any>".to_string())
                        }
                    } else {
                        Ok("list<any>".to_string())
                    }
                }
                "Option" => {
                    if let syn::PathArguments::AngleBracketed(args) =
                        &type_path.path.segments.last().unwrap().arguments
                    {
                        if let Some(syn::GenericArgument::Type(inner_ty)) = args.args.first() {
                            let inner_type = rust_type_to_wit(inner_ty, used_types)?;
                            Ok(format!("option<{}>", inner_type))
                        } else {
                            Ok("option<any>".to_string())
                        }
                    } else {
                        Ok("option<any>".to_string())
                    }
                }
                custom => {
                    // Validate custom type name
                    validate_name(custom, "Type")?;
                    
                    // Convert custom type to kebab-case and add to used types
                    let kebab_custom = to_kebab_case(custom);
                    used_types.insert(kebab_custom.clone());
                    Ok(kebab_custom)
                }
            }
        }
        Type::Reference(type_ref) => {
            // Handle references by using the underlying type
            rust_type_to_wit(&type_ref.elem, used_types)
        }
        Type::Tuple(type_tuple) => {
            if type_tuple.elems.is_empty() {
                // Empty tuple is unit in WIT
                Ok("unit".to_string())
            } else {
                // Create a tuple representation in WIT
                let mut elem_types = Vec::new();
                for elem in &type_tuple.elems {
                    elem_types.push(rust_type_to_wit(elem, used_types)?);
                }
                Ok(format!("tuple<{}>", elem_types.join(", ")))
            }
        }
        _ => Ok("unknown".to_string()),
    }
}

// Collect type definitions (structs and enums) from the file
fn collect_type_definitions(ast: &syn::File) -> Result<HashMap<String, String>> {
    let mut type_defs = HashMap::new();
    
    println!("Collecting type definitions from file");
    for item in &ast.items {
        match item {
            Item::Struct(item_struct) => {
                // Validate struct name doesn't contain numbers or "stream"
                let orig_name = item_struct.ident.to_string();
                validate_name(&orig_name, "Struct")?;
                
                // Use kebab-case for struct name
                let name = to_kebab_case(&orig_name);
                println!("  Found struct: {}", name);
                
                let fields: Vec<String> = match &item_struct.fields {
                    syn::Fields::Named(fields) => {
                        let mut used_types = HashSet::new();
                        let mut field_strings = Vec::new();
                        
                        for f in &fields.named {
                            if let Some(field_ident) = &f.ident {
                                // Validate field name doesn't contain digits
                                let field_orig_name = field_ident.to_string();
                                validate_name(&field_orig_name, "Field")?;
                                
                                // Convert field names to kebab-case
                                let field_name = to_kebab_case(&field_orig_name);
                                let field_type = rust_type_to_wit(&f.ty, &mut used_types)?;
                                println!("    Field: {} -> {}", field_name, field_type);
                                field_strings.push(format!("        {}: {}", field_name, field_type));
                            }
                        }
                        
                        field_strings
                    }
                    _ => Vec::new(),
                };
                
                if !fields.is_empty() {
                    type_defs.insert(
                        name.clone(),
                        format!("    record {} {{\n{}\n    }}", name, fields.join(",\n")), // Add comma separator
                    );
                }
            }
            Item::Enum(item_enum) => {
                // Validate enum name doesn't contain numbers or "stream"
                let orig_name = item_enum.ident.to_string();
                validate_name(&orig_name, "Enum")?;
                
                // Use kebab-case for enum name
                let name = to_kebab_case(&orig_name);
                println!("  Found enum: {}", name);
                
                let variants: Vec<String> = item_enum
                    .variants
                    .iter()
                    .map(|v| {
                        let variant_orig_name = v.ident.to_string();
                        // Validate variant name
                        validate_name(&variant_orig_name, "Enum variant")?;
                        
                        match &v.fields {
                            syn::Fields::Unnamed(fields) if fields.unnamed.len() == 1 => {
                                let mut used_types = HashSet::new();
                                let ty = rust_type_to_wit(
                                    &fields.unnamed.first().unwrap().ty,
                                    &mut used_types
                                )?;
                                
                                // Use kebab-case for variant names and use parentheses for type
                                let variant_name = to_kebab_case(&variant_orig_name);
                                println!("    Variant: {} -> {}", variant_name, ty);
                                Ok(format!("        {}({})", variant_name, ty))
                            }
                            syn::Fields::Unit => {
                                // Use kebab-case for variant names
                                let variant_name = to_kebab_case(&variant_orig_name);
                                println!("    Variant: {}", variant_name);
                                Ok(format!("        {}", variant_name))
                            },
                            _ => {
                                // Use kebab-case for variant names
                                let variant_name = to_kebab_case(&variant_orig_name);
                                println!("    Variant: {} (complex)", variant_name);
                                Ok(format!("        {}", variant_name))
                            },
                        }
                    })
                    .collect::<Result<Vec<String>>>()?;
                
                type_defs.insert(
                    name.clone(),
                    format!("    variant {} {{\n{}\n    }}", name, variants.join(",\n")), // Add comma separator
                );
            }
            _ => {}
        }
    }
    
    println!("Collected {} type definitions", type_defs.len());
    Ok(type_defs)
}

// Generate WIT content for an interface
fn generate_interface_wit_content(
    impl_item: &syn::ItemImpl,
    interface_name: &str,
    ast: &syn::File,
) -> Result<String> {
    let mut functions = Vec::new();
    let mut used_types = HashSet::new();
    
    // Extract the base name without "State" suffix for the interface
    let base_name = remove_state_suffix(interface_name);
    
    // Convert interface name to kebab-case for the interface declaration
    let kebab_interface_name = to_kebab_case(&base_name);
    println!("Generating WIT content for interface: {} (kebab: {})", interface_name, kebab_interface_name);
    
    for item in &impl_item.items {
        if let ImplItem::Fn(method) = item {
            let method_name = method.sig.ident.to_string();
            println!("  Examining method: {}", method_name);
            
            let has_remote = method.attrs.iter().any(|attr| attr.path().is_ident("remote"));
            let has_local = method.attrs.iter().any(|attr| attr.path().is_ident("local"));
            let has_http = method.attrs.iter().any(|attr| attr.path().is_ident("http"));
            
            let has_relevant_attr = has_remote || has_local || has_http;
            
            if has_relevant_attr {
                println!("    Has relevant attribute: {}", 
                    if has_remote { "remote" } 
                    else if has_local { "local" } 
                    else { "http" });
                
                let sig = &method.sig;
                
                // Validate function name
                validate_name(&method_name, "Function")?;
                
                // Convert function name to kebab-case
                let kebab_name = to_kebab_case(&method_name);
                println!("    Processing method: {} -> {}", method_name, kebab_name);
                
                let params: Vec<String> = sig
                    .inputs
                    .iter()
                    .filter_map(|arg| {
                        if let syn::FnArg::Typed(pat_type) = arg {
                            if let syn::Pat::Ident(pat_ident) = &*pat_type.pat {
                                // Skip &self and &mut self
                                if pat_ident.ident == "self" {
                                    println!("      Skipping self parameter");
                                    return None;
                                }
                                
                                // Get original param name and convert to kebab-case
                                let param_orig_name = pat_ident.ident.to_string();
                                
                                // Validate parameter name
                                match validate_name(&param_orig_name, "Parameter") {
                                    Ok(_) => {},
                                    Err(e) => return Some(Err(e)),
                                }
                                
                                let param_name = to_kebab_case(&param_orig_name);
                                
                                // Rust type to WIT type
                                match rust_type_to_wit(&pat_type.ty, &mut used_types) {
                                    Ok(param_type) => {
                                        println!("      Parameter: {} -> {}", param_name, param_type);
                                        Some(Ok(format!("{}: {}", param_name, param_type)))
                                    },
                                    Err(e) => Some(Err(e))
                                }
                            } else {
                                println!("      Skipping non-ident pattern");
                                None
                            }
                        } else {
                            println!("      Skipping non-typed argument");
                            None
                        }
                    })
                    .collect::<Result<Vec<String>>>()?;
                
                let return_type = match &sig.output {
                    syn::ReturnType::Type(_, ty) => {
                        let rt = rust_type_to_wit(&*ty, &mut used_types)?;
                        println!("      Return type: {} -> result<{}, string>", rt, rt);
                        format!("result<{}, string>", rt)
                    }
                    _ => {
                        println!("      Return type: unit -> result<unit, string>");
                        "result<unit, string>".to_string()
                    }
                };
                
                // Generate attribute comments with proper indentation
                let mut attr_comments = Vec::new();
                if has_remote {
                    attr_comments.push("    //remote");
                }
                if has_local {
                    attr_comments.push("    //local");
                }
                if has_http {
                    attr_comments.push("    //http");
                }
                let attr_comment_str = if !attr_comments.is_empty() {
                    format!("{}\n", attr_comments.join("\n"))
                } else {
                    String::new()
                };
                
                let func_sig = if params.is_empty() {
                    format!("{}    {}: func(target: address) -> {};", 
                        attr_comment_str,
                        kebab_name, 
                        return_type) 
                } else {
                    format!("{}    {}: func(target: address, {}) -> {};",
                        attr_comment_str,
                        kebab_name,
                        params.join(", "), // Use comma separator
                        return_type
                    ) 
                };
                
                println!("    Added function: {}", func_sig);
                functions.push(func_sig);
            } else {
                println!("    Skipping method without relevant attributes");
            }
        }
    }
    
    // Collect all type definitions from the file
    let all_type_defs = collect_type_definitions(ast)?;
    
    // Filter for only the types we're using
    let mut type_defs = Vec::new();
    let mut processed_types = HashSet::new();
    let mut types_to_process: Vec<String> = used_types.into_iter().collect();
    
    println!("Processing used types: {:?}", types_to_process);
    
    // Process all referenced types and their dependencies
    while let Some(type_name) = types_to_process.pop() {
        if processed_types.contains(&type_name) {
            continue;
        }
        
        processed_types.insert(type_name.clone());
        println!("  Processing type: {}", type_name);
        
        if let Some(type_def) = all_type_defs.get(&type_name) {
            println!("    Found type definition");
            type_defs.push(type_def.clone());
            
            // Extract any types referenced in this type definition
            for referenced_type in all_type_defs.keys() {
                if type_def.contains(referenced_type) && !processed_types.contains(referenced_type) {
                    println!("    Adding referenced type: {}", referenced_type);
                    types_to_process.push(referenced_type.clone());
                }
            }
        } else {
            println!("    No definition found for type: {}", type_name);
        }
    }
    
    // Generate the final WIT content
    if functions.is_empty() {
        println!("No functions found for interface {}", interface_name);
        Ok(String::new())
    } else {
        // Combine type definitions and functions within the interface block
        let combined_content = if type_defs.is_empty() {
            format!("    use standard.{{address}};\n\n{}", functions.join("\n"))
        } else {
            format!("    use standard.{{address}};\n\n{}\n\n{}", type_defs.join("\n\n"), functions.join("\n"))
        };
        
        let content = format!("interface {} {{\n{}\n}}\n", kebab_interface_name, combined_content);
        println!("Generated interface content for {} with {} type definitions", interface_name, type_defs.len());
        Ok(content)
    }
}

// Process a single Rust project and generate WIT files
fn process_rust_project(project_path: &Path, api_dir: &Path) -> Result<Option<(String, String)>> {
    println!("\nProcessing project: {}", project_path.display());
    let lib_rs = project_path.join("src").join("lib.rs");
    
    println!("Looking for lib.rs at {}", lib_rs.display());
    if !lib_rs.exists() {
        println!("No lib.rs found for project: {}", project_path.display());
        return Ok(None);
    }
    
    let lib_content = fs::read_to_string(&lib_rs)
        .with_context(|| format!("Failed to read lib.rs for project: {}", project_path.display()))?;
    
    println!("Successfully read lib.rs, parsing...");
    let ast = syn::parse_file(&lib_content)
        .with_context(|| format!("Failed to parse lib.rs for project: {}", project_path.display()))?;
    
    println!("Successfully parsed lib.rs");
    
    let mut wit_world = None;
    let mut interface_name = None;
    let mut kebab_interface_name = None;
    
    println!("Scanning for impl blocks with hyperprocess attribute");
    for item in &ast.items {
        if let Item::Impl(impl_item) = item {
            println!("Found impl block");
            
            // Check if this impl block has a #[hyperprocess] attribute
            if let Some(attr) = impl_item.attrs.iter().find(|attr| attr.path().is_ident("hyperprocess")) {
                println!("Found hyperprocess attribute");
                
                // Extract the wit_world name
                match extract_wit_world(&[attr.clone()]) {
                    Ok(world_name) => {
                        println!("Extracted wit_world: {}", world_name);
                        wit_world = Some(world_name);
                        
                        // Get the interface name from the impl type
                        interface_name = impl_item
                            .self_ty
                            .as_ref()
                            .as_type_path()
                            .map(|tp| {
                                if let Some(last_segment) = tp.path.segments.last() {
                                    last_segment.ident.to_string()
                                } else {
                                    "Unknown".to_string()
                                }
                            });
                        
                        // Check for "State" suffix and remove it
                        if let Some(ref name) = interface_name {
                            // Validate the interface name
                            validate_name(name, "Interface")?;
                            
                            // Remove State suffix if present
                            let base_name = remove_state_suffix(name);
                            
                            // Convert to kebab-case for file name and interface name
                            kebab_interface_name = Some(to_kebab_case(&base_name));
                            
                            println!("Interface name: {:?}", interface_name);
                            println!("Base name: {}", base_name);
                            println!("Kebab interface name: {:?}", kebab_interface_name);
                        }
                        
                        if let (Some(ref iface_name), Some(ref kebab_name)) = (&interface_name, &kebab_interface_name) {
                            // We already validated the interface name, so the file name should be fine
                            
                            // Generate the WIT content for the interface
                            let content = generate_interface_wit_content(impl_item, iface_name, &ast)?;
                            
                            if !content.is_empty() {
                                // Write the interface file with kebab-case name
                                let interface_file = api_dir.join(format!("{}.wit", kebab_name));
                                println!("Writing interface WIT file to {}", interface_file.display());
                                
                                fs::write(&interface_file, &content)
                                    .with_context(|| format!("Failed to write {}", interface_file.display()))?;
                                
                                println!("Successfully wrote interface WIT file");
                                
                                // Create and write the individual world file
                                let world_name = format!("{}-api-v0", kebab_name);
                                let world_content = format!("world {} {{\n    export {};\n}}\n", world_name, kebab_name);
                                let world_file = api_dir.join(format!("{}.wit", world_name));
                                
                                println!("Writing individual world WIT file to {}", world_file.display());
                                fs::write(&world_file, &world_content)
                                    .with_context(|| format!("Failed to write {}", world_file.display()))?;
                                
                                println!("Successfully wrote individual world WIT file");
                            } else {
                                println!("Generated WIT content is empty, skipping file creation");
                            }
                        }
                    },
                    Err(e) => println!("Failed to extract wit_world: {}", e),
                }
            }
        }
    }
    
    if let (Some(_main_world), Some(_), Some(kebab_iface)) = (wit_world, interface_name, kebab_interface_name) {
        println!("Returning import statement for interface {}", kebab_iface);
        // Return the kebab interface name and its corresponding individual world name
        let world_name = format!("{}-api-v0", kebab_iface);
        Ok(Some((kebab_iface, world_name)))
    } else {
        println!("No valid interface found");
        Ok(None)
    }
}

// Helper trait to get TypePath from Type
trait AsTypePath {
    fn as_type_path(&self) -> Option<&syn::TypePath>;
}

impl AsTypePath for syn::Type {
    fn as_type_path(&self) -> Option<&syn::TypePath> {
        match self {
            syn::Type::Path(tp) => Some(tp),
            _ => None,
        }
    }
}


fn generate_signatures() -> Result<()> {
    // Get the current working directory
    let cwd = std::env::current_dir()?;
    println!("Current working directory: {}", cwd.display());
    
    // Create the api directory if it doesn't exist
    let api_dir = cwd.join("api");
    println!("API directory: {}", api_dir.display());
    
    fs::create_dir_all(&api_dir)?;
    println!("Created or verified api directory");
    
    // Find all relevant Rust projects
    let projects = find_rust_projects(&cwd);
    
    if projects.is_empty() {
        println!("No relevant Rust projects found.");
        return Ok(());
    }
    
    println!("Found {} relevant Rust projects.", projects.len());
    
    // Process each project and collect world imports
    let mut world_imports = Vec::new();
    let mut main_world_name = None;
    
    for project_path in projects {
        println!("Processing project: {}", project_path.display());
        
        match process_rust_project(&project_path, &api_dir) {
            Ok(Some((interface_name, world_name))) => {
                println!("Got interface: {} and its world: {}", interface_name, world_name);
                // Import the interface directly in the main world (not the API world)
                world_imports.push(format!("    import {};", interface_name));
                
                // Extract the main world name from the first project (they should all use the same)
                if main_world_name.is_none() {
                    // Extract the main world from project
                    let lib_rs = project_path.join("src").join("lib.rs");
                    if let Ok(content) = fs::read_to_string(&lib_rs) {
                        if let Ok(ast) = syn::parse_file(&content) {
                            for item in &ast.items {
                                if let Item::Impl(impl_item) = item {
                                    if let Some(attr) = impl_item.attrs.iter().find(|attr| attr.path().is_ident("hyperprocess")) {
                                        if let Ok(world_name) = extract_wit_world(&[attr.clone()]) {
                                            main_world_name = Some(world_name);
                                            break;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            },
            Ok(None) => println!("No import statement generated"),
            Err(e) => println!("Error processing project: {}", e),
        }
    }
    
    println!("Collected {} world imports", world_imports.len());
    
    // Generate the main world file if we have imports
    if !world_imports.is_empty() {
        // Use default name if not found in any project
        let main_world = main_world_name.unwrap_or_else(|| "async-app-template-dot-os-v0".to_string());
        println!("Using main world name: {}", main_world);
        
        // Create main world content
        let world_content = format!(
            "world {} {{\n{}\n    include process-v1;\n}}",
            main_world,
            world_imports.join("\n") 
        );
        
        let world_file = api_dir.join(format!("{}.wit", main_world));
        println!("Writing main world definition to {}", world_file.display());
        
        fs::write(&world_file, world_content)
            .with_context(|| format!("Failed to write main world file: {}", world_file.display()))?;
        
        println!("Successfully created main world definition");
    }
    
    println!("WIT files generated successfully in the 'api' directory.");
    Ok(())
}

// Find all relevant Rust projects
fn find_rust_projects(base_dir: &Path) -> Vec<PathBuf> {
    let mut projects = Vec::new();
    println!("Scanning for Rust projects in {}", base_dir.display());
    
    for entry in WalkDir::new(base_dir)
        .max_depth(1)
        .into_iter()
        .filter_map(Result::ok)
    {
        let path = entry.path();
        
        if path.is_dir() && path != base_dir {
            let cargo_toml = path.join("Cargo.toml");
            println!("Checking {}", cargo_toml.display());
            
            if cargo_toml.exists() {
                // Try to read and parse Cargo.toml
                if let Ok(content) = fs::read_to_string(&cargo_toml) {
                    if let Ok(cargo_data) = content.parse::<Value>() {
                        // Check for the specific metadata
                        if let Some(metadata) = cargo_data
                            .get("package")
                            .and_then(|p| p.get("metadata"))
                            .and_then(|m| m.get("component"))
                        {
                            if let Some(package) = metadata.get("package") {
                                if let Some(package_str) = package.as_str() {
                                    println!("  Found package.metadata.component.package = {:?}", package_str);
                                    if package_str == "hyperware:process" {
                                        println!("  Adding project: {}", path.display());
                                        projects.push(path.to_path_buf());
                                    }
                                }
                            }
                        } else {
                            println!("  No package.metadata.component metadata found");
                        }
                    }
                }
            }
        }
    }
    
    println!("Found {} relevant Rust projects", projects.len());
    projects
}

fn main() -> Result<()> {
    generate_signatures()?;
    generate_implementations()?;
    Ok(())
}

#[derive(Clone)]
struct WitFunction {
    name: String,
    params: Vec<(String, String)>, // (name, type)
    return_type: String,
    attributes: Vec<String>, // local, remote, http, etc.
}

fn generate_implementations() -> Result<()> {
    // Get the current working directory
    let cwd = std::env::current_dir()?;
    println!("Current working directory: {}", cwd.display());
    
    // Create the target/wit directory if it doesn't exist
    let target_wit_dir = cwd.join("target").join("wit");
    println!("Target WIT directory: {}", target_wit_dir.display());
    
    fs::create_dir_all(&target_wit_dir)?;
    println!("Created or verified target/wit directory");
    
    // Get all generated API WIT files
    let api_dir = cwd.join("api");
    let mut api_interfaces = Vec::new();
    
    println!("Scanning for API WIT files in {}", api_dir.display());
    
    // Check if api directory exists
    if !api_dir.exists() {
        println!("API directory does not exist. Run the tool first to generate WIT files.");
        return Ok(());
    }
    
    // Iterate through the api directory
    for entry in fs::read_dir(&api_dir)? {
        let entry = entry?;
        let path = entry.path();
        
        if path.is_file() && path.extension().map_or(false, |ext| ext == "wit") {
            // Check if filename ends with -api-v0.wit
            let filename = path.file_stem().unwrap().to_string_lossy().to_string();
            if filename.ends_with("-api-v0") {
                println!("Found API WIT file: {}", path.display());
                
                // Extract interface name from the filename
                // Format is interface-name-api-v0.wit, so remove -api-v0 suffix
                let interface_name = filename.trim_end_matches("-api-v0");
                
                // Now prepare to copy it to target/wit
                fs::copy(&path, &target_wit_dir.join(path.file_name().unwrap()))?;
                
                // Copy the interface file as well
                let interface_filename = format!("{}.wit", interface_name);
                let interface_path = api_dir.join(&interface_filename);
                
                if interface_path.exists() {
                    println!("Copying interface file: {}", interface_path.display());
                    fs::copy(&interface_path, &target_wit_dir.join(&interface_filename))?;
                    
                    // Read interface file to extract function signatures
                    let interface_content = fs::read_to_string(&interface_path)?;
                    
                    // Add to our list of interfaces to process
                    api_interfaces.push((interface_name.to_string(), interface_content));
                } else {
                    println!("Interface file not found: {}", interface_path.display());
                }
            }
        }
    }
    
    // Now add the api crates to the workspace
    update_workspace_cargo_toml(&cwd, &api_interfaces)?;
    
    // Generate implementation crates
    for (interface_name, interface_content) in api_interfaces {
        generate_api_crate(&cwd, &interface_name, &interface_content)?;
    }
    
    println!("Implementation crates generated successfully.");
    Ok(())
}

fn update_workspace_cargo_toml(cwd: &Path, api_interfaces: &[(String, String)]) -> Result<()> {
    let cargo_toml_path = cwd.join("Cargo.toml");
    println!("Updating workspace Cargo.toml at {}", cargo_toml_path.display());
    
    if !cargo_toml_path.exists() {
        anyhow::bail!("Workspace Cargo.toml not found at {}", cargo_toml_path.display());
    }
    
    let cargo_content = fs::read_to_string(&cargo_toml_path)?;
    let mut cargo_toml: toml::Value = cargo_content.parse()?;
    
    // Get the current workspace members
    if let Some(workspace) = cargo_toml.get_mut("workspace") {
        if let Some(members) = workspace.get_mut("members") {
            if let Some(members_array) = members.as_array_mut() {
                let mut added_members = Vec::new();
                
                // Add each API interface crate if it's not already there
                for (interface_name, _) in api_interfaces {
                    let api_crate_name = format!("{}-api", interface_name);
                    
                    // Check if already in the members list
                    if !members_array.iter().any(|m| m.as_str().map_or(false, |s| s == api_crate_name)) {
                        println!("Adding {} to workspace members", api_crate_name);
                        members_array.push(toml::Value::String(api_crate_name.clone()));
                        added_members.push(api_crate_name);
                    }
                }
                
                // Sort the members array for consistency
                members_array.sort_by(|a, b| {
                    let a_str = a.as_str().unwrap_or("");
                    let b_str = b.as_str().unwrap_or("");
                    a_str.cmp(b_str)
                });
                
                if !added_members.is_empty() {
                    // Write the updated Cargo.toml
                    let updated_content = toml::to_string_pretty(&cargo_toml)?;
                    fs::write(&cargo_toml_path, updated_content)?;
                    println!("Added {} new members to workspace: {:?}", added_members.len(), added_members);
                } else {
                    println!("No new members added to workspace");
                }
            }
        }
    }
    
    Ok(())
}

fn generate_api_crate(cwd: &Path, interface_name: &str, interface_content: &str) -> Result<()> {
    let api_crate_name = format!("{}-api", interface_name);
    let api_crate_dir = cwd.join(&api_crate_name);
    
    println!("Generating API crate for {}", interface_name);
    
    // Create API crate directory
    fs::create_dir_all(&api_crate_dir)?;
    println!("Created directory: {}", api_crate_dir.display());
    
    // Create src directory
    let src_dir = api_crate_dir.join("src");
    fs::create_dir_all(&src_dir)?;
    println!("Created src directory: {}", src_dir.display());
    
    // Create Cargo.toml
    let cargo_toml_content = format!(r#"[package]
name = "{}"
version = "0.1.0"
edition = "2021"
publish = false

[dependencies]
anyhow = "1.0"
hyperware_process_lib = {{ version = "1.0.2", features = ["logging"] }}
process_macros = "0.1.0"
futures-util = "0.3"
serde = {{ version = "1.0", features = ["derive"] }}
serde_json = "1.0"
wit-bindgen = "0.36.0"
once_cell = "1.20.2"
futures = "0.3"
uuid = {{ version = "1.0" }}

[lib]
crate-type = ["cdylib"]

[package.metadata.component]
package = "hyperware:process"
"#, api_crate_name);
    
    let cargo_toml_path = api_crate_dir.join("Cargo.toml");
    fs::write(&cargo_toml_path, cargo_toml_content)?;
    println!("Created Cargo.toml: {}", cargo_toml_path.display());
    
    // Parse the interface content to extract function signatures and types
    let functions = extract_functions_from_interface(interface_content)?;
    
    // Generate lib.rs with implementations
    let lib_rs_content = generate_lib_rs_content(interface_name, &functions)?;
    
    let lib_rs_path = src_dir.join("lib.rs");
    fs::write(&lib_rs_path, lib_rs_content)?;
    println!("Created lib.rs: {}", lib_rs_path.display());
    
    println!("Successfully generated API crate: {}", api_crate_name);
    Ok(())
}

fn extract_functions_from_interface(interface_content: &str) -> Result<Vec<WitFunction>> {
    let mut functions = Vec::new();
    
    // Extract all lines containing function definitions
    let mut current_attributes = Vec::new();
    let lines: Vec<&str> = interface_content.lines().collect();
    
    for (i, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        
        // Check for attribute comments
        if trimmed.starts_with("//") {
            current_attributes.push(trimmed.trim_start_matches("//").trim().to_string());
            continue;
        }
        
        // Check for function definitions
        if trimmed.contains(": func(") && trimmed.contains(" -> ") {
            println!("Found function definition: {}", trimmed);
            
            // Parse the function name
            let name_end = trimmed.find(": func(").unwrap();
            let name = trimmed[..name_end].trim().to_string();
            
            // Parse parameters
            let params_start = trimmed.find('(').unwrap() + 1;
            let params_end = trimmed.find(") ->").unwrap();
            let params_str = &trimmed[params_start..params_end];
            
            // Parse return type
            let return_start = trimmed.find("-> ").unwrap() + 3;
            let return_end = if trimmed.contains(';') {
                trimmed.find(';').unwrap()
            } else {
                trimmed.len()
            };
            let return_type = trimmed[return_start..return_end].trim().to_string();
            
            // Process parameters
            let mut params = Vec::new();
            if !params_str.is_empty() {
                for param in params_str.split(',') {
                    let param_parts: Vec<&str> = param.split(':').collect();
                    if param_parts.len() == 2 {
                        let param_name = param_parts[0].trim().to_string();
                        let param_type = param_parts[1].trim().to_string();
                        
                        // Skip the "target: address" parameter as it's handled by the runtime
                        if param_name != "target" || param_type != "address" {
                            params.push((param_name, param_type));
                        }
                    }
                }
            }
            
            // Create function struct
            let func_attrs = current_attributes.clone();
            let wit_function = WitFunction {
                name,
                params,
                return_type,
                attributes: func_attrs,
            };
            
            functions.push(wit_function.clone());
            println!("Added function: {} with attributes: {:?}", wit_function.name, wit_function.attributes);
            
            // Clear attributes for next function
            current_attributes.clear();
        } else if !trimmed.is_empty() && !trimmed.starts_with("//") && 
                  !trimmed.starts_with("use ") && !trimmed.starts_with("interface ") && 
                  !trimmed.starts_with("record ") && !trimmed.starts_with("variant ") && 
                  !trimmed.starts_with("}") {
            // If not a function definition or a specific pattern we want to preserve attributes for,
            // clear any accumulated attributes
            current_attributes.clear();
        }
    }
    
    println!("Extracted {} functions", functions.len());
    Ok(functions)
}

fn generate_lib_rs_content(interface_name: &str, functions: &[WitFunction]) -> Result<String> {
    // Convert kebab-case to snake_case for the module name
    let snake_interface_name = interface_name.replace('-', "_");
    
    // Generate the world name (interface_name-api-v0)
    let world_name = format!("{}-api-v0", interface_name);
    
    // Start with the imports and wit-bindgen setup
    let mut content = format!(r#"use crate::exports::hyperware::process::{}::Guest;
use crate::exports::hyperware::process::{}::*;
use crate::hyperware::process::standard::Address as WitAddress;

wit_bindgen::generate!({{
    path: "target/wit",
    world: "{}",
    generate_unused_types: true,
    additional_derives: [serde::Deserialize, serde::Serialize, process_macros::SerdeJsonInto],
}});

struct Api;
impl Guest for Api {{
"#, snake_interface_name, snake_interface_name, world_name);
    
    // Add implementations for each function
    for function in functions {
        // Convert kebab-case function name to snake_case
        let snake_func_name = function.name.replace('-', "_");
        
        // Generate parameter list
        let mut param_list = Vec::new();
        param_list.push("target: WitAddress".to_string());
        
        for (param_name, param_type) in &function.params {
            // Convert kebab-case param name to snake_case
            let snake_param_name = param_name.replace('-', "_");
            
            // Convert kebab-case type names to PascalCase
            let rust_type = convert_wit_type_to_rust(param_type);
            
            param_list.push(format!("{}: {}", snake_param_name, rust_type));
        }
        
        // Parse return type
        let return_type = parse_wit_return_type(&function.return_type);
        
        // Generate function implementation
        let default_return = generate_default_return_value(&return_type);
        
        content.push_str(&format!(r#"    fn {}({}) -> {} {{
        {}{}
    }}
"#, 
            snake_func_name, 
            param_list.join(", "),
            return_type,
            // Add comment about implementation if there are attributes
            if !function.attributes.is_empty() {
                format!("        // {}\n        ", function.attributes.join(", "))
            } else {
                String::new()
            },
            default_return
        ));
    }
    
    // Add closing brace and export macro
    content.push_str("}\nexport!(Api);\n");
    
    Ok(content)
}

// Helper to generate default return values
fn generate_default_return_value(return_type: &str) -> String {
    if return_type.starts_with("Result<") {
        if return_type.contains("Result<(), ") {
            "Ok(())".to_string()
        } else if return_type.contains("Result<String, ") {
            "Ok(\"Success\".to_string())".to_string()
        } else if return_type.contains("Result<f32, ") || return_type.contains("Result<f64, ") {
            "Ok(0.0)".to_string()
        } else if return_type.contains("Result<i32, ") || return_type.contains("Result<u32, ") ||
                 return_type.contains("Result<i64, ") || return_type.contains("Result<u64, ") ||
                 return_type.contains("Result<s32, ") || return_type.contains("Result<s64, ") {
            "Ok(0)".to_string()
        } else if return_type.contains("Result<bool, ") {
            "Ok(true)".to_string()
        } else if return_type.contains("Result<Vec<") || return_type.contains("Result<List<") {
            "Ok(Vec::new())".to_string()
        } else if return_type.contains("Result<Option<") {
            "Ok(None)".to_string()
        } else {
            // For custom types in Result
            "Ok(Default::default())".to_string()
        }
    } else {
        // Direct return types
        match return_type {
            "()" => "()".to_string(),
            "String" | "string" => "\"Success\".to_string()".to_string(),
            "f32" | "f64" => "0.0".to_string(),
            "i32" | "u32" | "i64" | "u64" | "s32" | "s64" => "0".to_string(),
            "bool" => "true".to_string(),
            _ => {
                if return_type.starts_with("Vec<") || return_type.starts_with("List<") {
                    "Vec::new()".to_string()
                } else if return_type.starts_with("Option<") {
                    "None".to_string()
                } else {
                    "Default::default()".to_string()
                }
            }
        }
    }
}

// Parse WIT return type into Rust return type
fn parse_wit_return_type(wit_type: &str) -> String {
    if wit_type.starts_with("result<") {
        let inner = wit_type.trim_start_matches("result<").trim_end_matches(">");
        
        // Split by comma to get Ok and Err types
        let parts: Vec<&str> = inner.split(',').collect();
        
        if parts.len() == 2 {
            let ok_type = parts[0].trim();
            let err_type = parts[1].trim();
            
            // Convert WIT types to Rust types
            let ok_rust_type = convert_wit_type_to_rust(ok_type);
            let err_rust_type = convert_wit_type_to_rust(err_type);
            
            format!("Result<{}, {}>", ok_rust_type, err_rust_type)
        } else {
            // Fallback
            "Result<(), String>".to_string()
        }
    } else {
        // Direct mapping for non-result types
        convert_wit_type_to_rust(wit_type)
    }
}

// Convert WIT type to Rust type
fn convert_wit_type_to_rust(wit_type: &str) -> String {
    match wit_type.trim() {
        "unit" => "()".to_string(),
        "string" => "String".to_string(),
        "s32" => "i32".to_string(),
        "u32" => "u32".to_string(),
        "s64" => "i64".to_string(),
        "u64" => "u64".to_string(),
        "f32" => "f32".to_string(),
        "f64" => "f64".to_string(),
        "bool" => "bool".to_string(),
        _ => {
            // Check if it's a list type
            if wit_type.starts_with("list<") && wit_type.ends_with(">") {
                let inner_type = &wit_type[5..wit_type.len()-1];
                let rust_inner_type = convert_wit_type_to_rust(inner_type);
                format!("Vec<{}>", rust_inner_type)
            } 
            // Check if it's an option type
            else if wit_type.starts_with("option<") && wit_type.ends_with(">") {
                let inner_type = &wit_type[7..wit_type.len()-1];
                let rust_inner_type = convert_wit_type_to_rust(inner_type);
                format!("Option<{}>", rust_inner_type)
            }
            // Check if it's a tuple type
            else if wit_type.starts_with("tuple<") && wit_type.ends_with(">") {
                let inner_types = &wit_type[6..wit_type.len()-1];
                let rust_inner_types: Vec<String> = inner_types
                    .split(',')
                    .map(|t| convert_wit_type_to_rust(t.trim()))
                    .collect();
                format!("({})", rust_inner_types.join(", "))
            }
            // For custom types, use PascalCase
            else {
                to_pascal_case(&wit_type.replace('-', "_"))
            }
        }
    }
}

// Helper to convert a kebab-case or snake_case string to PascalCase
fn to_pascal_case(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    let mut capitalize_next = true;
    
    for c in s.chars() {
        if c == '_' || c == '-' {
            capitalize_next = true;
        } else if capitalize_next {
            result.push(c.to_uppercase().next().unwrap());
            capitalize_next = false;
        } else {
            result.push(c);
        }
    }
    
    result
}